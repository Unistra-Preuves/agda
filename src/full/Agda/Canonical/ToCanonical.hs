-- | Translation of an Agda goal into a Canonical problem.
--
--   The goal becomes a declaration named @Goal@ whose 'lets' contain
--   everything Canonical may use: the context variables, the lemmas given
--   by the user, and every datatype, constructor and function met while
--   translating them (with their clauses as rewrite rules and a generated
--   recursor for datatypes, see "Agda.Canonical.Recursor").
--
--   The translation functions thread the following state:
--
--   * the bound names @[String]@, the most recent first, so that the
--     de Bruijn index @i@ is the name at position @i@;
--
--   * the context @[CDecl]@ being built, the most recent declaration first
--     (it is reversed once, at the top level);
--
--   * the symbols already declared ('Seen'), to declare each symbol once and
--     to stop the recursion on recursive definitions;
--
--   * the signatures of the local variables (@Map String Sig@), used to
--     η-expand their arguments.
--
--   Canonical has no universe-polymorphic Π-type: a Π-type occurring as a
--   term is encoded with @Pi@, @Pi.mk@ and @Pi.f@ (see "Agda.Canonical.Builtin").

module Agda.Canonical.ToCanonical
  ( produceCanonicalGoal
  ) where

import Control.Monad (foldM, replicateM, zipWithM)
import Data.Foldable (foldlM)
import Data.Map (Map, insert)
import Data.Map qualified as Map
import Data.Maybe (catMaybes, isJust, isNothing)

import Agda.Canonical.Builtin
import Agda.Canonical.Cubical
import Agda.Canonical.Params (droppedParams, restoreTel, restoreTerm, restoreType)
import Agda.Canonical.Recursor (mkRecursor)
import Agda.Canonical.Types
import Agda.Canonical.Utils
import Agda.Syntax.Builtin
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty qualified as P
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Generic (foldTerm)
import Agda.Syntax.Internal.MetaVars (allMetasList, noMetas)
import Agda.Syntax.Internal.Names (namesIn)
import Agda.TypeChecking.Level (reallyUnLevelView)
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Free (freeIn)
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Context (addContext, inTopContext, underAbstraction)
import Agda.TypeChecking.Monad.MetaVars (lookupLocalMeta')
import Agda.TypeChecking.Monad.Signature (HasConstInfo (getConstInfo))
import Agda.TypeChecking.Reduce (instantiateFull, reduce)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope (teleNames, telView, telViewUpTo)
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Maybe (fromMaybe)
import Agda.Utils.Size (size)

---------------------------------------------------------------------------
-- * Goal
---------------------------------------------------------------------------

-- | The Canonical problem for a goal, and what is needed to print the answer.
--
--   The lemmas are declared before the context variables, the hypotheses
--   after them.  The goal is either declared directly, or through a
--   continuation (see "Goals with continuations").
produceCanonicalGoal
  :: [QName]                      -- ^ Lemmas given by the user.
  -> Telescope                    -- ^ Context of the goal.
  -> [(String, Type)]             -- ^ Hypotheses, with their types in that context.
  -> Type                         -- ^ Type of the goal, as a Π-type over the context.
  -> [([(Term, Bool)], Term)]     -- ^ Cubical boundary of the goal: for each face,
                                  --   the interval variables of the context set to
                                  --   @i0@ ('False') or @i1@ ('True'), and the term the
                                  --   goal is equal to there, in the context.
  -> (MetaId, [(Term, Term)])     -- ^ The meta of the hole, and the constraints of
                                  --   Agda @u = v@ on it, in the context.
  -> TCM (CDecl, GoalInfo)
produceCanonicalGoal lemmas ctx0 hyps0 ty0 bds (mv, cons) = do
  -- The parameters left out by Agda are put back (see "Agda.Canonical.Params").
  ctx  <- inTopContext $ restoreTel ctx0
  ty   <- inTopContext $ restoreType ty0
  hyps <- inTopContext $ addContext ctx0 $ mapM (traverse restoreType) hyps0
  cub <- isCubical
  -- In Cubical Agda, the interval and its primitives are always available.
  prims <- if not cub then return [] else
    catMaybes <$> mapM getPrimitiveName' [PrimIMin, PrimIMax, PrimINeg]
  (lets0, ald0) <- foldlM (\ (l, a) q -> gatherDatatypeInformations q [] l a)
                          ([typeDecl] ++ [iunivDecl | cub], seenFromList [typeSig]) (prims ++ lemmas)
  (ctx', ty', refolded) <- refoldBoundary (constrainedVars (size ctx) mv cons) ctx ty bds
  let m = length refolded
      -- A hypothesis that depends on a refolded variable cannot be declared.
      hyps' = [ (n, applySubst (strengthenS __IMPOSSIBLE__ m) a)
              | (n, a) <- hyps, not (any (`freeIn` a) [0 .. m - 1]) ]
      -- The constraints, on the meta applied to the refolded variables only.
      cons' = if m == 0 then [] else
                [ c | (u, v) <- cons
                    , Just c <- [ (,) <$> cutMeta (size ctx) m mv u <*> cutMeta (size ctx) m mv v ] ]
  aux hyps' refolded cons' ctx' ty' [] lets0 ald0 mempty
  where
    aux :: [(String, Type)] -> [String] -> [(Term, Term)] -> Telescope -> Type -> [String]
        -> [CDecl] -> Seen -> Map String Sig -> TCM (CDecl, GoalInfo)
    aux hs refolded cs tel t bindnames lets ald art =
      case tel of
        EmptyTel -> finish hs refolded cs t bindnames lets ald art
        ExtendTel dom (Abs nb b) ->
          case unEl t of
            Pi _ codom -> do
              (domdecl, lets', ald', art') <- toLetDecl (unEl $ unDom dom) nb [] bindnames lets ald False art
              aux hs refolded cs b (unAbs codom) (nb : bindnames) (domdecl : lets') ald' art'
            _ -> __IMPOSSIBLE__
        _ -> __IMPOSSIBLE__

    finish hs refolded cs t bindnames lets ald art = do
      (lets1, ald1, art1) <- foldlM (\ (l, a, r) (n, h) -> do
                                (d, l', a', r') <- toLetDecl (unEl h) n [] bindnames l a False r
                                return (d : l', a', r'))
                              (lets, ald, art) hs
      ms    <- fromMaybe [] <$> goalMetas t
      ends  <- pathEnds (unEl t)
      -- The first parameters stand for the refolded variables.
      sig   <- drop (length refolded) . termSig <$> inlinePaths (unEl t)
      -- The boundary of a parameter of path type is only a rewrite rule
      -- through a continuation, which declares it in the context.
      pathPar <- pathParam (unEl t)
      let info ald' art' cont = GoalInfo
            { giGlobals = seenSigs ald', giDefs = seenNames ald'
            , giLocals = insert "Goal" sig art'
            , giNames = reverse refolded ++ bindnames, giOutOfScope = []
            , giHyps = mempty, giCont = cont, giAliases = mempty
            , giRefold = refolded }
      if null ms && not (null cs) then do
        (res, cont, ald', art') <- constrainedGoal mv cs t bindnames lets1 ald1 art1
        return (res, info ald' art' (Just cont))
      else if null ms && isNothing ends && not pathPar then do
        (res, _, ald', art') <- toCDecl (unEl t) "Goal" [] bindnames lets1 ald1 True art1
        return (res, info ald' art' Nothing)
      else do
        (res, cont, ald', art') <- contGoal ms t 0 bindnames [] lets1 ald1 art1
        return (res, info ald' art' (Just cont))

-- ** Goals with continuations
--
-- Canonical only checks constraints on the parameters of a type, not on the
-- goal itself; and it cannot leave a variable to be found.  Some goals are
-- therefore stated through a continuation, following an encoding suggested
-- by Chase Norman:
--
-- > Goal : Δ → (k : (?m₁ : A₁) … (?mₙ : Aₙ) → (g : Θ → B) {constraints} → G) → G
--
-- where @G@ is a fresh opaque type, and the answer @λ Δ k → k t₁ … tₙ b@
-- gives the solution @λ Δ → b@ (see 'Agda.Canonical.FromCanonical.unwrapAnswer').
-- The binders @Δ@ are in fact declared in the context, as the variables
-- introduced by Agda, and the goal is only @(k : …) → G@: the equations of a
-- parameter are constraints on its instances, so the boundary of a path in
-- @Δ@ would not be a rewrite rule (e.g. @p x i0 ⤇ f x@ for
-- @p : (x : A) → f x ≡ g x@).  This is also why a goal with such a
-- parameter is stated through a continuation.
--
-- * __Metas.__  A goal whose type contains unsolved metas, such as
--   @_≡_ {A = ?A} 1 1@, asks Canonical to find the metas too.  Each meta
--   @?m@ is a function of the context in which it was created (Agda applies
--   it to the variables of that context), so it becomes a variable of its
--   closed type @A_m@, bound by the continuation; @tᵢ@ is the value of
--   @?mᵢ@.  The type of a meta may contain other metas: they come first.
--   @Δ@ is the longest prefix of the type of the goal without metas.  When
--   nothing else needs @g@, @b@ is given with the type @S@ constrained by
--   @S ≡ B@ instead, so that @B@ is only checked once the metas are known.
--
-- * __Paths__ (Cubical Agda).  If @B@ is a path type @PathP A x y@, @g@ is a
--   function of the interval with the constraints @g i0 ≡ x@ and
--   @g i1 ≡ y@ (see "Agda.Canonical.Cubical").
--
-- The constraints are only stated when they are closed (they cannot bind
-- variables).  A path of functions is therefore turned into a function to
-- paths, whose binders go to @Δ@ (see 'Agda.Canonical.Cubical.commutePath').
-- Agda checks the solution anyway.
--
-- The boundary of a hole in a clause with interval variables (@f p i = ?@)
-- is turned into path types beforehand, see 'refoldBoundary'.

-- | Refolds the end of the context, from the first interval variable
--   constrained by the boundary of the goal, into the type of the goal:
--   each refolded variable becomes a Π-binder, except an interval variable
--   with its two faces @i = i0 ⊢ u₀@ and @i = i1 ⊢ u₁@, which becomes the
--   path type @PathP (λ i → T) u₀ u₁@ (the faces of the outer variables are
--   abstracted over the inner ones).  In @funExt p i a = ?@, the goal
--   @B a@ with the boundary @i = i0 ⊢ f a@, @i = i1 ⊢ g a@ becomes
--   @f ≡ g@ in the context @p@.  The boundary is then stated by the
--   translation of paths, and the solution @λ i a → b@ is unfolded back
--   into @b@ (see 'Agda.Canonical.FromCanonical.unwrapAnswer').
--
--   At least the last @m0@ variables are refolded (see 'constrainedVars').
--   Returns the remaining context, the type of the goal over it, and the
--   names of the refolded variables (the first one first).  The faces
--   fixing several variables at once are ignored, and so is the boundary
--   outside of Cubical Agda.
refoldBoundary :: Int -> Telescope -> Type -> [([(Term, Bool)], Term)] -> TCM (Telescope, Type, [String])
refoldBoundary m0 ctx ty bds = do
  cub <- isCubical
  let n    = size ctx
      idxs = [ k | cub, (face, _) <- bds, (Var k [], _) <- face ]
      m    = maximum (m0 : [ 1 + k | k <- idxs ])
  if m == 0 || m > n then return (ctx, ty, []) else do
    TelV tel b <- telViewUpTo n ty
    if size tel /= n then return (ctx, ty, []) else do
      let doms  = drop (n - m) (telToList ctx)
          faces = [ (k, e, u) | ([(Var k [], e)], u) <- bds ]
          outer = telFromList (take (n - m) (telToList ctx))
      t <- refold doms b faces
      -- @telePi_@ keeps the unused binders, which the translation counts.
      return (outer, telePi_ outer t, map (fst . unDom) doms)
  where
    -- The innermost variable first; its faces are those of variable 0.
    refold :: [Dom (ArgName, Type)] -> Type -> [(Int, Bool, Term)] -> TCM Type
    refold [] t _ = return t
    refold ds t fs = do
      let d      = last ds
          (x, a) = unDom d
          face e = [ u | (0, e', u) <- fs, e' == e ]
          outer  = [ (k - 1, e, Lam (domInfo d) (Abs x u)) | (k, e, u) <- fs, k > 0 ]
      interval <- isIntervalType a
      t' <- case (interval, face False, face True) of
        (True, u0 : _, u1 : _) -> do
          zero  <- primIZero
          one   <- primIOne
          pathP <- fromMaybe __IMPOSSIBLE__ <$> getBuiltinName' builtinPathP
          let s = subst 0 zero (getSort t)
          l <- sortLevel s
          return $ El s $ Def pathP
            [ Apply (setHiding Hidden (defaultArg l))
            , Apply (defaultArg (Lam defaultArgInfo (Abs x (unEl t))))
            , Apply (defaultArg (subst 0 zero u0))
            , Apply (defaultArg (subst 0 one u1)) ]
        _ -> let dom = snd <$> d in return $ El (mkPiSort dom (Abs x t)) (Pi dom (Abs x t))
      refold (init ds) t' outer

-- *** Constraints on the meta of the hole
--
-- Agda may have constraints on the meta of the hole that are not part of its
-- boundary, e.g. @p (?0 (i = i1)) = x@ and @p (?0 (i = i0)) = y@ for
-- @sym p i = p ?@: there the meta is applied to the context with some
-- variables substituted.  The context is refolded from the first substituted
-- variable, the solution @g@ becomes a function of the refolded variables,
-- and each constraint, with the meta applied to them only, becomes a
-- constraint on @g@ (@p (g i1) ⤇ x@), stated through a continuation:
--
-- > Goal : (k : (g : Θ → B) {constraints} → G) → G
--
-- A constraint that still mentions a refolded variable is dropped, since
-- it would bind it.

-- | The number of variables at the end of the context (of size @n@) that the
--   constraints substitute in the applications of the meta @mv@: in
--   @?0 ℓ A x y p i1@, the argument @i1@ stands for the variable @i@.
constrainedVars :: Int -> MetaId -> [(Term, Term)] -> Int
constrainedVars n mv cons = maximum (0 : [ n - prefix es | es <- occs ])
  where
    occs = foldTerm (\case MetaV m es | m == mv -> [es]; _ -> []) cons
    -- The number of leading arguments that are the variables themselves.
    prefix es = length (takeWhile id (zipWith isSelf [0 ..] es))
      where isSelf j e = j < n && case e of
              Apply a | Var k [] <- unArg a -> k == n - 1 - j
              _                             -> False

-- | @cutMeta n m mv t@ applies each occurrence of the meta @mv@ in @t@ (in a
--   context of size @n@) to its last @m@ arguments only, and strengthens
--   @t@ away from the last @m@ variables.  'Nothing' if an occurrence is not
--   applied to the first @n - m@ variables themselves, or if @t@ still
--   mentions the last @m@ variables.
cutMeta :: Int -> Int -> MetaId -> Term -> Maybe Term
cutMeta n m mv t0 = do
  t <- go 0 t0
  if any (`freeIn` t) [0 .. m - 1] then Nothing
  else Just (applySubst (strengthenS __IMPOSSIBLE__ m) t)
  where
    k = n - m
    go :: Int -> Term -> Maybe Term
    go d t = case t of
      MetaV x es | x == mv -> do
        as <- mapM isApply es
        if length as /= n || or [ unArg a /= Var (n - 1 - j + d) [] | (j, a) <- zip [0 ..] (take k as) ]
          then Nothing
          else MetaV x . map Apply <$> mapM (traverse (go d)) (drop k as)
      MetaV x es  -> MetaV x <$> goEs d es
      Var i es    -> Var i <$> goEs d es
      Def q es    -> Def q <$> goEs d es
      Con c i es  -> Con c i <$> goEs d es
      Lam i b     -> Lam i <$> goAbs d b
      Pi a b      -> Pi <$> traverse (goT d) a <*> goAbsT d b
      Lit{}       -> Just t
      _ | mv `elem` allMetasList t -> Nothing
        | otherwise                -> Just t
    goEs d = mapM $ \case
      Apply a      -> Apply <$> traverse (go d) a
      IApply x y r -> IApply <$> go d x <*> go d y <*> go d r
      e            -> Just e
    goT d (El s u) = El s <$> go d u
    goAbs d (Abs x u)    = Abs x <$> go (d + 1) u
    goAbs d (NoAbs x u)  = NoAbs x <$> go d u
    goAbsT d (Abs x u)   = Abs x <$> goT (d + 1) u
    goAbsT d (NoAbs x u) = NoAbs x <$> goT d u
    isApply (Apply a) = Just a
    isApply _         = Nothing

-- | The goal of a hole with constraints, see "Constraints on the meta of
--   the hole".  @t@ is the type of the solution, a function of the refolded
--   variables; the solution is named after the meta, which the
--   constraints apply to them.
constrainedGoal
  :: MetaId -> [(Term, Term)] -> Type -> [String] -> [CDecl] -> Seen -> Map String Sig
  -> TCM (CDecl, Cont, Seen, Map String Sig)
constrainedGoal mv cs t bindnames lets ald art = do
  let g = metaVarName mv
  art0 <- (\ s -> insert g s art) . termSig <$> inlinePaths (unEl t)
  (gd, lets1, ald1, _) <- toCDecl (unEl t) g [] bindnames lets ald False art0
  (eqs, lets2, ald2) <- foldlM (\ (es, ls, al) (u, v) -> do
                          (eu, ls1, al1) <- toCExpr u bindnames [] ls al False False art0
                          (ev, ls2, al2) <- toCExpr v bindnames [] ls1 al1 False False art0
                          return ( es ++ [ CEquation (spine eu) (spine ev) True
                                         | null (params eu), null (params ev) ]
                                 , ls2, al2 ))
                        ([], lets1, ald1) cs
  [gN, k] <- mapM freshString ["G", "k"]
  let kDecl = typed k (CExpr [gd { equations = equations gd ++ eqs }] [] (simpleSpine gN))
      lets3 = CDecl gN Nothing [] : lets2
      goal  = CExpr [kDecl] (reverse lets3) (simpleSpine gN)
      cont  = Cont { contOuter = [], contMetas = [], contTyped = False, contSwap = 0 }
  return (CDecl "Goal" (Just goal) [], cont, ald2, art0)

-- | Is the type the interval @I@?
isIntervalType :: Type -> TCM Bool
isIntervalType a = reduce (unEl a) >>= \case
  Def q [] -> isInterval q
  _        -> return False

-- | The unsolved metas of a type, with their closed types, each one after
--   the metas its type contains.  'Nothing' if one of them is not a local
--   meta with a type (e.g. a sort meta).
goalMetas :: Type -> TCM (Maybe [(MetaId, Type)])
goalMetas t = do
  t' <- instantiateFull t
  go [] (allMetasList t')
  where
    go done [] = return (Just done)
    go done (m : ms)
      | m `elem` map fst done = go done ms
      | otherwise = do
          mv <- lookupLocalMeta' m
          case mvJudgement <$> mv of
            Just HasType{ jMetaType = a0 } -> do
              a <- inTopContext . restoreType =<< instantiateFull a0
              -- The metas of its type first.
              mdone <- go done (filter (`notElem` map fst done) (allMetasList a))
              case mdone of
                Nothing    -> return Nothing
                Just done' -> go (done' ++ [(m, a)]) ms
            _ -> return Nothing

-- | Does the type have a parameter of path type (Cubical Agda)?
pathParam :: Term -> TCM Bool
pathParam t = case t of
  Pi a b -> do
    here <- isJust <$> pathEnds (unEl (unDom a))
    if here then return True else pathParam (unEl (unAbs b))
  _ -> return False

-- | The goal through a continuation, see "Goals with continuations".
--   Returns the goal, the shape of the answer, and the updated 'Seen' and
--   signatures.
contGoal
  :: [(MetaId, Type)]  -- ^ The metas, with their closed types, in order.
  -> Type              -- ^ The rest of the type of the goal.
  -> Int               -- ^ The number of binders of @Δ@ coming from a path of functions.
  -> [String]          -- ^ Bound names.
  -> [CDecl]           -- ^ Binders of @Δ@ already met, the most recent first.
  -> [CDecl]           -- ^ Context.
  -> Seen
  -> Map String Sig    -- ^ Signatures of the local variables.
  -> TCM (CDecl, Cont, Seen, Map String Sig)
contGoal ms t swaps bindnames pidecl lets ald art = do
  t' <- instantiateFull t
  ends <- pathEnds (unEl t')
  let isPi = case unEl t' of { Pi{} -> True; _ -> False }
  -- A path of functions is a function to paths: its binders go to @Δ@.
  commuted <- if not isPi && isJust ends then commutePath (unEl t')
              else return Nothing
  case (commuted, unEl t') of
    (Just u, _) -> contGoal ms (t' { unEl = u }) (swaps + 1) bindnames pidecl lets ald art
    (_, Pi a b) | swaps > 0 || noMetas (unDom a) -> do
      (newnames, na) <- case b of
        NoAbs n _ -> do n' <- freshString (anonName n); return (bindnames, n')
        Abs n _   -> do n' <- freshString n;   return (n' : bindnames, n')
      -- The binder is declared in the context, as the variables
      -- introduced by Agda: the equations of a parameter are only
      -- constraints on its instances, so the boundary of a path would not
      -- be a rewrite rule.
      (domdecl, lets1, ald1, art1) <- toLetDecl (unEl $ unDom a) na [] bindnames lets ald False art
      contGoal ms (unAbs b) swaps newnames (domdecl : pidecl) (domdecl : lets1) ald1 art1
    _ -> do
      -- The metas, as variables of their closed types.
      msigs <- mapM (\ (m, a) -> (,) (metaVarName m) . termSig <$> inlinePaths (unEl a)) ms
      let art0 = foldr (uncurry insert) art msigs
      (mdecls, lets1, ald1) <- foldlM (\ (ds, ls, al) (m, a) -> do
                                  (d, ls', al', _) <- toCDecl (unEl a) (metaVarName m) [] [] ls al False art0
                                  return (ds ++ [d], ls', al'))
                                ([], lets, ald) ms
      let useS = isNothing ends
      (final, lets2, ald2) <-
        if useS then do
          -- @S ≡ B@, @b : S@.
          (eb, ls1, al1) <- toCExpr (unEl t') bindnames [] lets1 ald1 False False art0
          lv <- sortLevel (getSort t')
          (el, ls2, al2) <- toCExpr lv bindnames [] ls1 al1 False False art0
          [sN, v] <- mapM freshString ["S", "s"]
          return ( [ CDecl sN (Just (CExpr [] [] (CSpine "Type" [el])))
                           [CEquation (simpleSpine sN) (spine eb) True]
                   , typed v (simpleExpr sN) ]
                 , ls2, al2 )
        else do
          -- @g : B@, with the boundary of @B@, a path.
          g <- freshString "g"
          (gd, ls1, al1, _) <- toCDecl (unEl t') g [] bindnames lets1 ald1 False art0
          return ([gd], ls1, al1)
      [gN, k] <- mapM freshString ["G", "k"]
      let kDecl = typed k (CExpr (mdecls ++ final) [] (simpleSpine gN))
          lets3 = CDecl gN Nothing [] : lets2
          goal  = CExpr [kDecl] (reverse lets3) (simpleSpine gN)
          cont  = Cont { contOuter = map name (reverse pidecl), contMetas = map fst ms
                       , contTyped = useS, contSwap = swaps }
      return (CDecl "Goal" (Just goal) [], cont, ald2, art0)

-- | Declares the interval, and returns the names of @i0@ and @i1@.
intervalEnds :: [CDecl] -> Seen -> TCM (String, String, [CDecl], Seen)
intervalEnds lets ald = do
  iq  <- fromMaybe __IMPOSSIBLE__ <$> getBuiltinName' builtinInterval
  i0q <- fromMaybe __IMPOSSIBLE__ <$> getBuiltinName' builtinIZero
  i1q <- fromMaybe __IMPOSSIBLE__ <$> getBuiltinName' builtinIOne
  (lets', ald') <- gatherDatatypeInformations iq [] lets ald
  return (nameToString i0q, nameToString i1q, lets', ald')

---------------------------------------------------------------------------
-- * Signatures
---------------------------------------------------------------------------

-- | Signatures of a symbol.
data Sym = Sym
  { symSig  :: Sig
      -- ^ Aligned with the eliminations in Agda terms: for a constructor,
      --   without the parameters of its datatype.
  , symTy   :: Maybe Type
      -- ^ Type of a definition, to compute the types of its arguments.
  , symDecl :: Sig
      -- ^ As declared to Canonical; this is the one stored in 'Seen'.
  }

-- | A local variable: both signatures agree, its type is unknown.
localSym :: Sig -> Sym
localSym s = Sym s Nothing s

-- | The name of a non-dependent binder: the one written by the user
--   (@(p : x ≡ y) → …@), or @a@ for an anonymous one (@A → B@).
anonName :: ArgName -> String
anonName n
  | null n || n == "_" = "a"
  | otherwise          = n

-- | Number of Π-binders of a term.
arityOf :: Term -> Int
arityOf (Pi _ b) = 1 + arityOf (unEl (unAbs b))
arityOf _        = 0

-- | Syntactic signature of a type (aliases are not unfolded).
termSig :: Term -> Sig
termSig (Pi a b) = Param (arityOf (unEl (unDom a))) (getHiding a) : termSig (unEl (unAbs b))
termSig _        = []

-- | Signature of a closed type, unfolding aliases with 'telView'.
tySig :: Type -> TCM Sig
tySig t = do
  t' <- inlinePaths (unEl t)
  TelV tel _ <- telView (El (getSort t) t')
  go tel
  where
    go :: Telescope -> TCM Sig
    go EmptyTel = return []
    go (ExtendTel dom b) = do
      TelV d _ <- telView (unDom dom)
      rest <- underAbstraction dom b go
      return (Param (size d) (getHiding dom) : rest)

-- | A definition, with the metas solved since it was checked instantiated
--   (e.g. the implicit arguments in the type of a postulate of the file).
constInfo :: QName -> TCM Definition
constInfo q = instantiateFull =<< getConstInfo q

-- | Signatures of a definition or a constructor.
globalSym :: QName -> TCM Sym
globalSym q = do
  def <- constInfo q
  sg  <- tySig (defType def)
  case theDef def of
    ConstructorDefn cd -> return (Sym (drop (_conPars cd) sg) Nothing sg)
    _                  -> do
      ty <- restoredType def
      return (Sym sg (Just ty) sg)

---------------------------------------------------------------------------
-- * Π-types as terms
---------------------------------------------------------------------------

-- | Declares @Pi@, and @Level@ and @_⊔_@ on which it depends, if not done yet.
withPi :: [CDecl] -> Seen -> TCM ([CDecl], Seen)
withPi lets ald
  | "Pi" `seenMember` ald = return (lets, ald)
  | otherwise = do
      lq <- fromMaybe __IMPOSSIBLE__ <$> getName' BuiltinLevel
      mq <- fromMaybe __IMPOSSIBLE__ <$> getName' PrimLevelMax
      let ald0 = foldr (uncurry seenInsert) ald piSigs
      (lets1, ald1) <- foldlM (\ (l, a) q -> gatherDatatypeInformations q [] l a)
                              (lets, ald0) [lq, mq]
      return (piDecls ++ lets1, ald1)

-- | The common arguments of @Pi@, @Pi.mk@ and @Pi.f@.
data PiP = PiP
  { ppLu :: CExpr  -- ^ Level of the domain.
  , ppLv :: CExpr  -- ^ Level of the codomain.
  , ppA  :: CExpr  -- ^ Domain.
  , ppB  :: CExpr  -- ^ Codomain, as a family @λ x. B@.
  }

-- | The arguments of a 'PiP', in order.
piArgs :: PiP -> [CExpr]
piArgs p = [ppLu p, ppLv p, ppA p, ppB p]

-- | Level of a sort; 'lzero' for the sorts Canonical does not know.
sortLevel :: Sort -> TCM Term
sortLevel (Type l) = reallyUnLevelView l
sortLevel (SSet l) = reallyUnLevelView l
sortLevel _        = return (Level (Max 0 []))

-- | Translates the components of a Π-type @(x : A) → B@.
piParts :: Dom Type -> Abs Type -> [String] -> [CDecl] -> Seen -> Map String Sig
        -> TCM (PiP, [CDecl], Seen)
piParts a b names lets ald art = do
  (nm, names') <- case b of
    NoAbs _ _ -> (\ n -> (n, names))        <$> freshString "a"
    Abs n _   -> (\ n' -> (n', n' : names)) <$> freshString n
  lu <- sortLevel (getSort (unDom a))
  lv <- sortLevel (getSort (unAbs b))
  (eu, l1, a1) <- toCExpr lu names  [] lets ald False False art
  (ev, l2, a2) <- toCExpr lv names' [] l1   a1  False False art
  (ea, l3, a3) <- toCExpr (unEl $ unDom a) names [] l2 a2 False False art
  let art' = Map.insert nm (termSig (unEl $ unDom a)) art
  (eb, l4, a4) <- toCExpr (unEl $ unAbs b) names' [CDecl nm Nothing []] l3 a3 False False art'
  (l5, a5) <- withPi l4 a4
  return (PiP eu ev ea eb, l5, a5)

---------------------------------------------------------------------------
-- * Applications
---------------------------------------------------------------------------

-- | The terms of the applications in a list of eliminations.
appliedTerms :: [Elim' Term] -> [Term]
appliedTerms es = concatMap arg es
  where
    arg (Apply t)      = [unArg t]
    arg (IApply _ _ r) = [r]   -- a path is a function of the interval
    arg _              = []

-- | The successive function types before each argument, instantiated.
fnTypes :: Type -> [Term] -> [Type]
fnTypes t (a : as)
  | Pi _ b <- unEl t = t : fnTypes (absApp b a) as
fnTypes _ _ = []

-- | @stripPi ps ns t@ removes @length ps@ Π-binders from @t@, binding their
--   variables to the names @ps@ (pushed onto the bound names @ns@).
stripPi :: [String] -> [String] -> Term -> Maybe ([String], Term)
stripPi [] ns t = Just (ns, t)
stripPi (p : ps) ns (Pi _ b) = case b of
  Abs _ _   -> stripPi ps (p : ns) (unEl (unAbs b))
  NoAbs _ _ -> stripPi ps ns (unEl (unAbs b))
stripPi _ _ _ = Nothing

-- | Adapts an argument to the expected arity @k@.
--
--   With fewer binders, it is η-expanded.  With more binders, the extra ones
--   are wrapped in @Pi.mk@: the parameter has a Π-type as a term.
fixArg :: [String] -> Int -> Maybe Term -> CExpr -> [CDecl] -> Seen -> Map String Sig
       -> TCM (CExpr, [CDecl], Seen)
fixArg names k mty ce@(CExpr ps ls sp) lets ald art
  | m == k = return (ce, lets, ald)
  | m < k  = do
      ce' <- etaExtend (k - m) ce
      return (ce', lets, ald)
  | otherwise =
      case mty >>= stripPi (map name outer) names of
        Just (names', Pi dom b) -> do
          (pp, lets1, ald1) <- piParts dom b names' lets ald art
          (inner', lets2, ald2) <- fixArg names' 1 (Just (Pi dom b)) (CExpr inner [] sp) lets1 ald1 art
          return (CExpr outer ls (CSpine "Pi.mk" (piArgs pp ++ [inner'])), lets2, ald2)
        _ -> return (ce, lets, ald)
  where
    m = length ps
    (outer, inner) = splitAt k ps

-- | Applies a head symbol to its translated arguments, in η-long form.
--
--   Each argument is adapted to the arity expected by the signature
--   ('fixArg').  Missing arguments become fresh binders, returned so that
--   the caller adds them to the enclosing λ.  Arguments beyond the
--   signature (the head returns a Π-type as a term) are applied with @Pi.f@.
applyHead
  :: String          -- ^ Head symbol.
  -> Maybe Sym       -- ^ Its signatures, if known.
  -> [Term]          -- ^ The Agda arguments.
  -> [CExpr]         -- ^ The same arguments, translated.
  -> [String]        -- ^ Bound names.
  -> [CDecl]         -- ^ Context.
  -> Seen
  -> Map String Sig  -- ^ Signatures of the local variables.
  -> TCM (CSpine, [CDecl], [CDecl], Seen)
       -- ^ The spine, the binders added by η-expansion, the context and 'Seen'.
applyHead hd Nothing _ cargs _ lets ald _ =
  return (CSpine hd cargs, [], lets, ald)
applyHead hd (Just Sym { symSig = sg, symTy = mty }) terms cargs names lets0 ald0 art = do
  let ar   = length sg
      n    = length cargs
      ftys = maybe [] (`fnTypes` terms) mty
      expTy i = case drop i ftys of
        (t : _) | Pi dom _ <- unEl t -> Just (unEl (unDom dom))
        _                            -> Nothing
      fixStep (acc, ls, al) (i, k, ce) = do
        (ce', ls', al') <- fixArg names k (expTy i) ce ls al art
        return (acc ++ [ce'], ls', al')
      exStep (g, ls, al) (i, ce) =
        case drop i ftys of
          (t : _) | Pi dom b <- unEl t -> do
            let dty = unEl (unDom dom)
            (pp, ls1, al1)  <- piParts dom b names ls al art
            (ce', ls2, al2) <- fixArg names (arityOf dty) (Just dty) ce ls1 al1 art
            return (CSpine "Pi.f" (piArgs pp ++ [CExpr [] [] g, ce']), ls2, al2)
          _ -> return (appendArg g ce, ls, al)
  (fixed, lets1, ald1) <- foldM fixStep ([], lets0, ald0) (zip3 [0 ..] (map pArity sg) cargs)
  xs   <- replicateM (max 0 (ar - n)) (freshString "x")
  etas <- zipWithM etaVar xs (map pArity (drop n sg))
  (sp, lets2, ald2) <- foldM exStep (CSpine hd (fixed ++ etas), lets1, ald1)
                                    (zip [ar ..] (drop ar cargs))
  return (sp, map (\ x -> CDecl x Nothing []) xs, lets2, ald2)
  where
    appendArg (CSpine h as) ce = CSpine h (as ++ [ce])

---------------------------------------------------------------------------
-- * Terms
---------------------------------------------------------------------------

-- | Translates a type into the declaration of a parameter, and records its
--   signature.
--
--   In Cubical Agda, the path types in type positions become functions of
--   the interval; if the type is a path type @PathP A x y@, its boundary
--   @n i0 ≡ x@, @n i1 ≡ y@ is added as constraints (see 'pathEquations').
toCDecl
  :: Term            -- ^ The type of the declaration.
  -> String          -- ^ Its name.
  -> [CEquation]     -- ^ Its equations.
  -> [String]        -- ^ Bound names.
  -> [CDecl]         -- ^ Context.
  -> Seen
  -> Bool            -- ^ Is it the goal (the context is then attached to it)?
  -> Map String Sig  -- ^ Signatures of the local variables.
  -> TCM (CDecl, [CDecl], Seen, Map String Sig)
toCDecl = toDecl False

-- | 'toCDecl' for a declaration of the context, whose equations are rewrite
--   rules: the boundary of a path is added even below Π-binders.
toLetDecl
  :: Term -> String -> [CEquation] -> [String] -> [CDecl] -> Seen -> Bool -> Map String Sig
  -> TCM (CDecl, [CDecl], Seen, Map String Sig)
toLetDecl = toDecl True

-- | 'toCDecl' and 'toLetDecl'.
toDecl :: Bool -> Term -> String -> [CEquation] -> [String] -> [CDecl] -> Seen -> Bool -> Map String Sig
       -> TCM (CDecl, [CDecl], Seen, Map String Sig)
toDecl isLet t0 n eqs bindnames lets ald tplvl art = do
  t <- inlinePaths t0
  (ty, lets1, ald1) <- toCExpr t bindnames [] lets ald tplvl True art
  (peqs, lets2, ald2) <- if tplvl then return ([], lets1, ald1)
                         else pathEquations isLet n ty t0 bindnames lets1 ald1 art
  return ( CDecl { name = n, typ = Just ty, equations = eqs ++ peqs }
         , lets2, ald2, insert n (termSig t) art )

-- | The boundary of a declaration @n : Δ → PathP A x y@, translated as
--   @n : Δ → (i : I) → A i@ with the type @ty@:
--
--   > n δ i0 ⤇ x        n δ i1 ⤇ y
--
--   η-expanded if @A@ is a function type.  As constraints (not 'isLet'),
--   these equations cannot bind variables: they are only given when @Δ@
--   and the arguments of @A@ are empty.
pathEquations :: Bool -> String -> CExpr -> Term -> [String] -> [CDecl] -> Seen -> Map String Sig
              -> TCM ([CEquation], [CDecl], Seen)
pathEquations isLet n ty t0 bindnames lets ald art = do
  ends <- pathEnds t0
  case ends of
    Just (k, x, y) | length (params ty) > k -> do
      (i0, i1, lets1, ald1) <- intervalEnds lets ald
      let outer = map name (take k (params ty))
          extra = length (params ty) - k - 1
          names = reverse outer ++ bindnames
          end (es, ls, al) (i, u) = do
            (eu, ls', al') <- toCExpr u names [] ls al False False art
            eu' <- etaTo extra eu
            let xs  = map name (params eu')
                lhs = CSpine n (map simpleExpr (outer ++ [i] ++ xs))
                ok  = length xs == extra && (isLet || (k == 0 && extra == 0))
            return (es ++ [ CEquation lhs (spine eu') True | ok ], ls', al')
      foldlM end ([], lets1, ald1) [(i0, x), (i1, y)]
    _ -> return ([], lets, ald)

-- | Translates a term.
--
--   In a type position, Π-binders become parameters; elsewhere, a Π-type is
--   encoded with @Pi@.  λ-binders always become parameters.
toCExpr
  :: Term            -- ^ The term.
  -> [String]        -- ^ Bound names.
  -> [CDecl]         -- ^ Parameters already met, the most recent first.
  -> [CDecl]         -- ^ Context.
  -> Seen
  -> Bool            -- ^ Is it the goal (the context is then attached to it)?
  -> Bool            -- ^ Is it in a type position?
  -> Map String Sig  -- ^ Signatures of the local variables.
  -> TCM (CExpr, [CDecl], Seen)
toCExpr t bindnames pidecl letdecl ald tplvl totyp art =
  case t of
    Pi a b | totyp -> do
      (newnames, na) <- case b of
        NoAbs n _ -> do n' <- freshString (anonName n); return (bindnames, n')
        Abs n _   -> do n' <- freshString n;   return (n' : bindnames, n')
      (domdecl, lets, ald', art') <- toCDecl (unEl $ unDom a) na [] bindnames letdecl ald False art
      toCExpr (unEl $ unAbs b) newnames (domdecl : pidecl) lets ald' tplvl totyp art'
    Pi a b -> do
      (pp, lets, ald') <- piParts a b bindnames letdecl ald art
      return ( CExpr (reverse pidecl) (if tplvl then reverse lets else []) (CSpine "Pi" (piArgs pp))
             , lets, ald' )
    Lam _ b -> do
      let (newnames, n) = case b of
            NoAbs _ _ -> (bindnames, "_")
            Abs x _   -> (x : bindnames, x)
      toCExpr (unAbs b) newnames (CDecl n Nothing [] : pidecl) letdecl ald tplvl False art
    _ -> do
      (sp, extra, lets, ald') <- toCSpine t bindnames letdecl ald art
      return ( CExpr { params = reverse pidecl ++ extra
                     , lets   = if tplvl then reverse lets else []
                     , spine  = sp }
             , lets, ald' )

-- | Translates a neutral term or a sort.
--
--   Returns the binders added by η-expansion (see 'applyHead').
--   Unsupported terms are kept as their printed form.
toCSpine :: Term -> [String] -> [CDecl] -> Seen -> Map String Sig
         -> TCM (CSpine, [CDecl], [CDecl], Seen)
toCSpine t bindnames lets ald art =
  case t of
    Var i el -> do
      (as, lets', ald') <- elimsToCExpr el bindnames lets ald art
      let h = bindnames !! i
      applyHead h (localSym <$> Map.lookup h art) (appliedTerms el) as bindnames lets' ald' art
    Sort (Type l) -> do
      t' <- reallyUnLevelView l
      (a, lets', ald') <- toCExpr t' bindnames [] lets ald False False art
      return (CSpine { head = "Type", args = [a] }, [], lets', ald')
    Sort (SSet l) -> do
      t' <- reallyUnLevelView l
      (a, lets', ald') <- toCExpr t' bindnames [] lets ald False False art
      return (CSpine { head = "ß", args = [a] }, [], lets', ald')
    Sort IntervalUniv ->
      return (CSpine { head = "IUniv", args = [] }, [], lets, ald)
    Level l -> do
      t' <- reallyUnLevelView l
      toCSpine t' bindnames lets ald art
    Def qname e -> do
      (as, lets1, ald1) <- elimsToCExpr e bindnames lets ald art
      (lets2, ald2) <- gatherDatatypeInformations qname bindnames lets1 ald1
      sym <- globalSym qname
      def <- constInfo qname
      -- A constructor applied to the parameters of its datatype (see
      -- "Agda.Canonical.Params").
      sym' <- case theDef def of
        ConstructorDefn{} -> do
          ty <- restoredType def
          return sym { symSig = symDecl sym, symTy = Just ty }
        _ -> return sym
      applyHead (nameToString qname) (Just sym') (appliedTerms e) as bindnames lets2 ald2 art
    MetaV m e -> do
      -- A meta of the goal (see "Goals with metas"), applied to its context.
      let h = metaVarName m
      (as, lets', ald') <- elimsToCExpr e bindnames lets ald art
      applyHead h (localSym <$> Map.lookup h art) (appliedTerms e) as bindnames lets' ald' art
    Con hd _ e -> do
      infos <- getConstInfo (conName hd)
      let dataname = case theDef infos of
            ConstructorDefn cd -> _conData cd
            _                  -> __IMPOSSIBLE__
      (as, lets1, ald1) <- elimsToCExpr e bindnames lets ald art
      (lets2, ald2) <- gatherDatatypeInformations dataname bindnames lets1 ald1
      sym <- globalSym (conName hd)
      applyHead (nameToString (conName hd)) (Just sym) (appliedTerms e) as bindnames lets2 ald2 art
    _ -> return (CSpine { head = P.prettyShow t, args = [] }, [], lets, ald)

-- | Translates the arguments of a list of eliminations.
--
--   The application of a path to an interval term is an ordinary application
--   (see "Agda.Canonical.Cubical").  Projections are not supported; they are
--   kept as their printed form.
elimsToCExpr :: [Elim' Term] -> [String] -> [CDecl] -> Seen -> Map String Sig
             -> TCM ([CExpr], [CDecl], Seen)
elimsToCExpr es names lets ald art =
  case es of
    [] -> return ([], lets, ald)
    el : els -> do
      (e',   lets1, ald1) <- elimToCExpr el lets ald
      (els', lets2, ald2) <- elimsToCExpr els names lets1 ald1 art
      return (e' : els', lets2, ald2)
  where
    elimToCExpr :: Elim' Term -> [CDecl] -> Seen -> TCM (CExpr, [CDecl], Seen)
    elimToCExpr c ls al =
      case c of
        Apply t        -> toCExpr (unArg t) names [] ls al False False art
        IApply _ _ r   -> toCExpr r names [] ls al False False art
        _              -> return (simpleExpr (P.prettyShow c), ls, al)

---------------------------------------------------------------------------
-- * Definitions
---------------------------------------------------------------------------

-- | Declares a definition (and what it depends on) to Canonical, if not
--   done yet.
--
--   * A datatype comes with its constructors and its recursor.
--   * A function comes with its clauses, as rewrite rules.
--   * @_⊔_@ comes with 'levelMaxEqs'.
gatherDatatypeInformations
  :: QName     -- ^ The definition.
  -> [String]  -- ^ Bound names.
  -> [CDecl]   -- ^ Context.
  -> Seen
  -> TCM ([CDecl], Seen)
gatherDatatypeInformations qn bindnames lets ald =
  if nameToString qn `seenMember` ald then return (lets, ald)
  else do
    def <- constInfo qn
    case theDef def of
      -- A constructor is declared with its datatype.
      ConstructorDefn cd -> gatherDatatypeInformations (_conData cd) bindnames lets ald
      _ -> do
        sym <- globalSym qn
        dty <- restoredType def
        let alrd = seenInsertDef (nameToString qn) qn (symDecl sym) ald
        (eqs, lets0, ald0) <- builtinEqs (nameToString qn) lets alrd
        (ty', lets1, ald1, _) <- toLetDecl (unEl dty) (nameToString qn) eqs bindnames lets0 ald0 False mempty
        let letss = ty' : lets1
        case theDef def of
          DatatypeDefn dd@DatatypeData { _dataCons = cons } -> do
            defs <- mapM constInfo cons
            syms <- mapM globalSym cons
            ctys0 <- mapM restoredType defs
            let names = map nameToString cons
                tys   = zip (map unEl ctys0) names
                alrd2 = foldl (\ m (k, q, s) -> seenInsertDef k q (symDecl s) m) ald1 (zip3 names cons syms)
            (ctys, lets2, ald2) <- foldlM (\ (acc, ls, al) (t, n) -> do
                                      (nt, ls', al', _) <- toLetDecl t n [] bindnames ls al False mempty
                                      return (nt : acc, ls', al'))
                                    ([], letss, alrd2) tys
            let ctorDs = reverse ctys
            lq <- fromMaybe __IMPOSSIBLE__ <$> getName' BuiltinLevel
            (lets3, ald3) <- gatherDatatypeInformations lq [] lets2 ald2
            -- The interval cannot be eliminated.
            interval <- isInterval qn
            mrec <- if interval then return Nothing else mkRecursor (_dataPars dd) ty' ctorDs
            case mrec of
              Nothing        -> return (ctorDs ++ lets3, ald3)
              Just (recD, s) -> return (recD : ctorDs ++ lets3, seenInsert (name recD) s ald3)
          FunctionDefn FunctionData { _funClauses = cls } -> do
            (eqs', lets2, ald2) <- clausesToEquations qn (symDecl sym) (droppedParams (theDef def)) cls lets1 ald1
            return (ty' { equations = equations ty' ++ eqs' } : lets2, ald2)
          _ -> do
            -- @PathP@ comes with @Path.mk@ and @Path.f@.
            pathP <- (Just qn ==) <$> getBuiltinName' builtinPathP
            cub   <- isCubical
            if not (pathP && cub) then return (letss, ald1) else do
              iq <- fromMaybe __IMPOSSIBLE__ <$> getBuiltinName' builtinInterval
              (i0, i1, lets2, ald2) <- intervalEnds letss ald1
              return ( pathDecls (nameToString qn) (nameToString iq) i0 i1 ++ lets2
                     , foldr (uncurry seenInsert) ald2 pathSigs )

-- | The type of a definition, with the parameters left out by Agda put back
--   (see "Agda.Canonical.Params").
restoredType :: Definition -> TCM Type
restoredType def = inTopContext $ restoreType (defType def)

-- | The rules of a symbol that Agda computes with internally: @_⊔_@ on
--   levels, and the primitives on the interval in Cubical Agda.
builtinEqs :: String -> [CDecl] -> Seen -> TCM ([CEquation], [CDecl], Seen)
builtinEqs n lets ald
  | n == "_⊔_" = return (levelMaxEqs, lets, ald)
  | n `elem` ["primIMin", "primIMax", "primINeg"] = do
      cub <- isCubical
      if not cub then return ([], lets, ald) else do
        (i0, i1, lets', ald') <- intervalEnds lets ald
        return (intervalEqs i0 i1 n, lets', ald')
  | otherwise = return ([], lets, ald)

-- ** Clauses

-- | Translates the clauses of a function, skipping the unsupported ones.
clausesToEquations :: QName -> Sig -> Int -> [Clause] -> [CDecl] -> Seen
                   -> TCM ([CEquation], [CDecl], Seen)
clausesToEquations qn sg np cls lets ald =
  foldlM (\ (eqs, ls, al) cl -> do
            (me, ls', al') <- clauseToEquation qn sg np cl ls al
            return (eqs ++ maybe [] pure me, ls', al'))
         ([], lets, ald) cls

-- | Translates a clause into a rewrite rule, in η-long form.
--
--   The parameters dropped by Agda from the clauses of a projection or of a
--   projection-like function (see "Agda.Canonical.Params") become
--   wildcards: its body does not use them.
--
--   The clause is skipped ('Nothing') if it has no body, an unsupported
--   pattern, or more patterns than the signature, or if its body contains an
--   unsolved meta or uses a function that the user cannot write (see 'isHidden').
clauseToEquation :: QName -> Sig -> Int -> Clause -> [CDecl] -> Seen
                 -> TCM (Maybe CEquation, [CDecl], Seen)
clauseToEquation qn sg np cl lets ald =
  case clauseBody cl of
    Nothing   -> skip
    Just body0 -> do
      -- A body that is still a hole, or contains one, is not a definition yet.
      body1  <- instantiateFull body0
      hidden <- or <$> mapM isHidden (namesIn body1 :: [QName])
      if hidden || not (noMetas body1) then skip else do
        let tel  = clauseTel cl
            pats = map namedArg (namedClausePats cl)
            ar   = length sg
            n    = np + length pats
        body <- inTopContext $ addContext tel $ restoreTerm (unArg <$> clauseType cl) body1
        ns <- mapM freshString (teleNames tel)
        sigs <- mapM (fmap termSig . inlinePaths . unEl . snd . unDom) (telToList tel)
        let bindn = reverse ns                       -- Var i is bindn !! i
            art0  = Map.fromList (zip ns sigs)
        ws  <- replicateM np (Just . simpleExpr <$> freshString "p")
        mps <- (ws ++) <$> mapM (patToCExpr bindn) pats
        case sequence mps of
          Just lhs0 | n <= ar -> do
            l                 <- zipWithM etaTo (map pArity sg) lhs0
            (xs, bindn', b')  <- peel (ar - n) bindn body
            (e, lets', ald')  <- toCExpr b' bindn' [] lets ald False False art0
            let k = ar - n - length xs
                j = length (params e)
            if j > k then skip else do
              e' <- etaExtend (k - j) e
              let extra = map simpleExpr (xs ++ map name (params e'))
              return ( Just (CEquation (CSpine (nameToString qn) (l ++ extra)) (spine e') True)
                     , lets', ald' )
          _ -> skip
  where skip = return (Nothing, lets, ald)

-- | A pattern-matching lambda or the auxiliary function of a @with@: their
--   names cannot be written in Agda, so a solution must not unfold to them.
isHidden :: QName -> TCM Bool
isHidden q = do
  d <- theDef <$> getConstInfo q
  return $ case d of
    Function { funExtLam = Just _ } -> True
    Function { funWith = Just _ }   -> True
    _                               -> False

-- | Translates a pattern into an argument of a left-hand side.
--
--   A dot pattern becomes a fresh wildcard; the parameters of a constructor,
--   absent from Agda patterns, become fresh wildcards; an interval pattern
--   (@f p i = …@) is a variable.  Literals, projections and the other
--   cubical patterns are not supported ('Nothing').
patToCExpr :: [String] -> DeBruijnPattern -> TCM (Maybe CExpr)
patToCExpr names p = case p of
  VarP _ x -> return . Just $ simpleExpr (names !! dbPatVarIndex x)
  IApplyP _ _ _ x -> return . Just $ simpleExpr (names !! dbPatVarIndex x)
  DotP _ _ -> Just . simpleExpr <$> freshString "w"
  ConP c _ ps -> do
    np   <- conParCount (conName c)
    ws   <- replicateM np (simpleExpr <$> freshString "p")
    subs <- mapM (patToCExpr names . namedArg) ps
    return $ (\ ss -> CExpr [] [] (CSpine (nameToString (conName c)) (ws ++ ss)))
               <$> sequence subs
  _ -> return Nothing

-- | Number of parameters of the datatype of a constructor.
conParCount :: QName -> TCM Int
conParCount q = do
  d <- getConstInfo q
  return $ case theDef d of
    ConstructorDefn cd -> _conPars cd
    _                  -> __IMPOSSIBLE__

-- | @peel k ns t@ removes up to @k@ λ-binders of @t@ with fresh names.
--   Returns these names, the extended bound names, and the body.
peel :: Int -> [String] -> Term -> TCM ([String], [String], Term)
peel k ns (Lam _ b) | k > 0 = do
  let nm = case b of { Abs n _ -> n; NoAbs n _ -> n }
  x <- freshString nm
  let ns' = case b of { Abs{} -> x : ns; NoAbs{} -> ns }
  (xs, ns'', t) <- peel (k - 1) ns' (unAbs b)
  return (x : xs, ns'', t)
peel _ ns t = return ([], ns, t)
