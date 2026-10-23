-- | Translation of an Agda goal into a Canonical problem.
--
--   The goal becomes a declaration named @Goal@ whose 'lets' contain
--   everything Canonical may use: the context variables, the lemmas given
--   by the user, and every datatype, constructor and function met while
--   translating them (with their clauses as rewrite rules and a generated
--   recursor for datatypes, see "Agda.Canonical.Recursor").
--
--   The translation runs in 'TransM', whose state is the context being
--   built and the symbols already declared ('Seen'): each symbol is declared
--   once, which also stops the recursion on recursive definitions.  The
--   translation functions take as arguments
--
--   * the bound names @[String]@, the most recent first, so that the
--     de Bruijn index @i@ is the name at position @i@;
--
--   * the signatures of the local variables ('Locals'), used to η-expand
--     their arguments.
--
--   Canonical has no universe-polymorphic Π-type: a Π-type occurring as a
--   term is encoded with @Pi@, @Pi.mk@ and @Pi.f@ (see "Agda.Canonical.Builtin").

module Agda.Canonical.ToCanonical
  ( produceCanonicalGoal
  , undeclaredSymbols
  ) where

import Control.Monad (foldM, forM, guard, replicateM, unless, when, zipWithM, (<=<))
import Control.Monad.Except (catchError)
import Control.Monad.State (StateT, evalStateT, get, gets, lift, modify, put)
import Control.Monad.Trans.Maybe (MaybeT (..))
import Data.List (isSuffixOf, mapAccumL)
import Data.Functor ((<&>))
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (catMaybes, isJust, isNothing, listToMaybe)
import Data.Set (Set)
import Data.Set qualified as Set

import Agda.Canonical.Builtin
import Agda.Canonical.Cubical
import Agda.Canonical.Params (droppedParams, restoreEquation, restoreTel, restoreTerm, restoreType)
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
import Agda.Syntax.Literal (Literal (..))
import Agda.TypeChecking.Level (reallyUnLevelView)
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Free (Free, freeIn)
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Context (addContext, inTopContext, underAbstraction)
import Agda.TypeChecking.Monad.MetaVars (lookupLocalMeta')
import Agda.TypeChecking.Monad.Pure (PureTCM)
import Agda.TypeChecking.Monad.Signature (HasConstInfo (getConstInfo))
import Agda.TypeChecking.Reduce (instantiateFull, reduce)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope (teleNames, telView, telViewUpTo)
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Maybe (fromMaybe, whenJust)
import Agda.Utils.Monad (anyM)
import Agda.Utils.Size (size)

---------------------------------------------------------------------------
-- * The translation monad
---------------------------------------------------------------------------

-- | What the translation accumulates.
data TransState = TransState
  { tsContext :: [CDecl]
      -- ^ The context being built, the most recent declaration first (it is
      --   reversed once, when it is attached to the goal).
  , tsSeen    :: Seen
      -- ^ The symbols already declared.
  }

-- | The translation.
type TransM = StateT TransState TCM

-- | Adds declarations to the context, the first one being the most recent.
pushDecls :: [CDecl] -> TransM ()
pushDecls ds = modify $ \ s -> s { tsContext = ds ++ tsContext s }

-- | Adds a declaration to the context.
pushDecl :: CDecl -> TransM ()
pushDecl d = pushDecls [d]

-- | The context built so far, in order.
currentContext :: TransM [CDecl]
currentContext = gets (reverse . tsContext)

-- | The symbols already declared.
getSeen :: TransM Seen
getSeen = gets tsSeen

-- | Records declared symbols.
modifySeen :: (Seen -> Seen) -> TransM ()
modifySeen f = modify $ \ s -> s { tsSeen = f (tsSeen s) }

-- | Runs a translation that may give up.  If it does, what it has declared
--   is forgotten.
attempt :: MaybeT TransM a -> TransM (Maybe a)
attempt m = do
  s <- get
  r <- runMaybeT m
  when (isNothing r) $ put s
  return r

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
  -> [(String, Type, Maybe Term)] -- ^ Hypotheses, with their types in that context, and
                                  --   their values for @let@-bound variables.
  -> Type                         -- ^ Type of the goal, as a Π-type over the context.
  -> [([(Term, Bool)], Term)]     -- ^ Cubical boundary of the goal: for each face,
                                  --   the interval variables of the context set to
                                  --   @i0@ ('False') or @i1@ ('True'), and the term the
                                  --   goal is equal to there, in the context.
  -> (MetaId, [(Term, Term)])     -- ^ The meta of the hole, and the constraints of
                                  --   Agda @u = v@ on it, in the context.
  -> TCM (CDecl, GoalInfo)
produceCanonicalGoal lemmas ctx0 hyps0 ty0 bds (mv, cons0) = do
  -- The parameters left out by Agda are put back (see "Agda.Canonical.Params").
  ctx  <- inTopContext $ restoreTel ctx0
  ty   <- inTopContext $ restoreType ty0
  hyps <- inTopContext $ addContext ctx0 $ forM hyps0 $ \ (n, a, mv') ->
            (,,) n <$> restoreType a <*> traverse (restoreTerm (Just a)) mv'
  cons <- inTopContext $ addContext ctx0 $
            mapM (uncurry restoreEquation) cons0
  cub <- isCubical
  -- In Cubical Agda, the interval and its primitives are always available.
  prims <- if not cub then return [] else
    catMaybes <$> mapM getPrimitiveName' [PrimIMin, PrimIMax, PrimINeg]
  let start = TransState
        { tsContext = [typeDecl] ++ [iunivDecl | cub]
        , tsSeen    = seenFromList [typeSig] }
  flip evalStateT start $ do
    mapM_ declareDef (prims ++ lemmas)
    (ctx', ty', refolded) <- lift $ refoldBoundary (constrainedVars (size ctx) mv cons) ctx ty bds
    let m   = length refolded
        rho = strengthenS __IMPOSSIBLE__ m
        mentionsRefolded :: Free a => a -> Bool
        mentionsRefolded u = any (`freeIn` u) [0 .. m - 1]
        -- A hypothesis that depends on a refolded variable cannot be
        -- declared; neither may the value of a @let@ (it is then left out).
        hyps' = [ (n, applySubst rho a, applySubst rho <$> v)
                | (n, a, v0) <- hyps, not (mentionsRefolded a)
                , let v = v0 >>= \ u -> if mentionsRefolded u then Nothing else Just u ]
        -- The constraints, on the meta applied to the refolded variables only
        -- (to none of them, e.g. @?1 = 3@ once @?0 + ?1 = 3@ is reduced),
        -- without other metas (e.g. @?0 + ?1 = 3@ for @?0@).
        cons' = [ c | (u, v) <- cons, all (== mv) (allMetasList (u, v))
                , Just c <- [ (,) <$> cutMeta (size ctx) m mv u <*> cutMeta (size ctx) m mv v ] ]
    (t, names, locals0) <- declareContext ctx' ty' [] Map.empty
    locals <- foldM (declareHypothesis names) locals0 hyps'
    ms      <- lift $ fromMaybe [] <$> goalMetas t
    ends    <- pathEnds (unEl t)
    -- The first parameters stand for the refolded variables.
    sig     <- drop (length refolded) . termSig <$> inlinePaths (unEl t)
    -- The boundary of a parameter of path type is only a rewrite rule
    -- through a continuation, which declares it in the context.
    pathPar <- pathParam (unEl t)
    (goal, cont, locals') <- if
      | null ms, not (null cons') -> do
          (g, c, l) <- constrainedGoal mv cons' t names locals
          return (g, Just c, l)
      | null ms, isNothing ends, not pathPar -> do
          g <- directGoal t names locals
          return (g, Nothing, locals)
      | otherwise -> do
          (g, c, l) <- contGoal ms t 0 names [] locals
          return (g, Just c, l)
    seen <- getSeen
    return (goal, emptyGoalInfo
      { giContext = maybe [] lets (typ goal)
      , giGlobals = seenSigs seen, giDefs = seenNames seen
      , giLocals  = Map.insert "Goal" sig (Map.map fst locals')
      , giNames   = reverse refolded ++ names
      , giCont    = cont
      , giRefold  = refolded })

-- | The heads of the types of a problem that are not declared, which
--   Canonical would reject: an internal error of the translation.
--
--   As in Canonical, the parameters and the definitions of an expression
--   are all in scope in their types and in its body.  The equations are
--   not checked: their names that are not in scope are pattern variables.
undeclaredSymbols :: CDecl -> [String]
undeclaredSymbols = Set.toList . decl Set.empty
  where
    decl :: Set String -> CDecl -> Set String
    decl sc = maybe Set.empty (expr sc) . typ
    expr :: Set String -> CExpr -> Set String
    expr sc (CExpr ps ls sp) = Set.unions (spineS sc' sp : map (decl sc') (ps ++ ls))
      where sc' = Set.union sc (Set.fromList (map name (ps ++ ls)))
    spineS :: Set String -> CSpine -> Set String
    spineS sc (CSpine h as) =
      Set.unions ([ Set.singleton h | h `Set.notMember` sc ] ++ map (expr sc) as)

-- | Declares the variables of the context, in order, and returns the type of
--   the goal over the rest of the telescope, the bound names and the
--   signatures of the variables.
declareContext :: Telescope -> Type -> [String] -> Locals -> TransM (Type, [String], Locals)
declareContext tel t names locals = case (tel, unEl t) of
  (EmptyTel, _) -> return (t, names, locals)
  (ExtendTel dom (Abs x tel'), Pi _ cod) -> do
    (d, locals') <- declare Definition (unEl (unDom dom)) x [] names locals
    pushDecl d
    declareContext tel' (unAbs cod) (x : names) locals'
  _ -> __IMPOSSIBLE__

-- | Declares an induction hypothesis, or a @let@-bound variable: the value
--   of a @let@ without metas is a rewrite rule.
declareHypothesis :: [String] -> Locals -> (String, Type, Maybe Term) -> TransM Locals
declareHypothesis names locals (n, a, mv) = do
  eqs <- case mv of
    Just v | noMetas v -> do
      ev <- toCExpr v names locals
      return [ CEquation (simpleSpine n) (spine ev) True | null (params ev) ]
    _ -> return []
  (d, locals') <- declare Definition (unEl a) n eqs names locals
  pushDecl d
  return locals'

-- | The goal declared directly, with the context attached to its type.
directGoal :: Type -> [String] -> Locals -> TransM CDecl
directGoal t names locals = do
  t' <- lift $ unfoldPis =<< inlinePaths (unEl t)
  ty <- toCType t' names locals
  ctx <- currentContext
  return $ typed "Goal" ty { lets = ctx }

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

-- | @Goal : (k : ps → G) → G@ for a fresh opaque type @G@, with the context
--   attached.
continuation :: [CDecl] -> TransM CDecl
continuation ps = do
  g <- freshString "G"
  k <- freshString "k"
  pushDecl (untyped g)
  ctx <- currentContext
  return $ typed "Goal" $ CExpr [typed k (CExpr ps [] (simpleSpine g))] ctx (simpleSpine g)

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
constrainedVars n mv cons = maximum (0 : [ n - prefix d es | (d, es) <- occs ])
  where
    occs = concat [ metaOccs mv 0 u ++ metaOccs mv 0 v | (u, v) <- cons ]
    -- The number of leading arguments that are the variables themselves,
    -- under @d@ binders.
    prefix d es = length (takeWhile id (zipWith isSelf [0 ..] es))
      where isSelf j e = j < n && case e of
              Apply a | Var k [] <- unArg a -> k == n - 1 - j + d
              _                             -> False

-- | The occurrences of a meta in a term, with their eliminations and the
--   number of binders above them.
metaOccs :: MetaId -> Int -> Term -> [(Int, Elims)]
metaOccs mv = go
  where
    go d t = case t of
      MetaV m es -> [ (d, es) | m == mv ] ++ goEs d es
      Var _ es   -> goEs d es
      Def _ es   -> goEs d es
      Con _ _ es -> goEs d es
      Lam _ b    -> goAbs d b
      Pi a b     -> go d (unEl (unDom a)) ++ goAbs d (unEl <$> b)
      Level l    -> foldTerm (\case MetaV m es | m == mv -> [(d, es)]; _ -> []) l
      _          -> []
    goEs d = concatMap $ \case
      Apply a      -> go d (unArg a)
      IApply x y r -> go d x ++ go d y ++ go d r
      _            -> []
    goAbs d (Abs _ u)   = go (d + 1) u
    goAbs d (NoAbs _ u) = go d u

-- | @cutMeta n m mv t@ applies each occurrence of the meta @mv@ in @t@ (in a
--   context of size @n@) to its arguments after the first @n - m@ only (the
--   last @m@ of the context, and the ones beyond it), and strengthens
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
        if length as < n || or [ unArg a /= Var (n - 1 - j + d) [] | (j, a) <- zip [0 ..] (take k as) ]
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
  :: MetaId -> [(Term, Term)] -> Type -> [String] -> Locals
  -> TransM (CDecl, Cont, Locals)
constrainedGoal mv cs t names locals = do
  let g = metaVarName mv
  locals' <- (\ s -> Map.insert g (s, Nothing) locals) . termSig <$> inlinePaths (unEl t)
  (gd, _) <- declare Parameter (unEl t) g [] names locals'
  (eqs, aux) <- unzip <$> mapM (constraint locals') cs
  -- The opaque symbols of the latest constraints are the most recent.
  pushDecls (concat (reverse aux))
  goal <- continuation [gd { equations = equations gd ++ eqs }]
  return (goal, Cont { contOuter = [], contMetas = [], contTyped = False, contSwap = 0 }, locals')
  where
    -- Both sides of an equation are spines: an equation between functions
    -- (@?0 x = λ h → h x@) is stated under a fresh opaque symbol
    -- @W : (f : (h : _) → G') → G'@, whose arguments are compared under the
    -- same binders, @W (λ h → g x h) ⤇ W (λ h → h x)@.  Returns the
    -- declarations of @W@ and @G'@, the most recent first.
    constraint locals' (u, v) = do
      eu0 <- toCExpr u names locals'
      ev0 <- toCExpr v names locals'
      let n = max (length (params eu0)) (length (params ev0))
      eu <- etaExtend (n - length (params eu0)) eu0
      ev <- etaExtend (n - length (params ev0)) ev0
      if n == 0 then return (CEquation (spine eu) (spine ev) True, []) else do
        w  <- freshString "W"
        gW <- freshString "G"
        let fty = CExpr (map (untyped . name) (params eu)) [] (simpleSpine gW)
            wd  = typed w (CExpr [typed "f" fty] [] (simpleSpine gW))
        return (CEquation (CSpine w [eu]) (CSpine w [ev]) True, [wd, untyped gW])

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
      | otherwise = closedMetaType m >>= \case
          Just a -> do
            -- The metas of its type first.
            mdone <- go done (filter (`notElem` map fst done) (allMetasList a))
            case mdone of
              Nothing    -> return Nothing
              Just done' -> go (done' ++ [(m, a)]) ms
          Nothing -> return Nothing

-- | The type of a meta, closed over the context in which it was created,
--   with the metas solved since instantiated.  'Nothing' if it is not a
--   local meta with a type (e.g. a sort meta).
closedMetaType :: MetaId -> TCM (Maybe Type)
closedMetaType m = lookupLocalMeta' m >>= \case
  Just MetaVar{ mvJudgement = HasType{ jMetaType = a } } ->
    Just <$> (inTopContext . restoreType =<< instantiateFull a)
  _ -> return Nothing

-- | Does the type have a parameter of path type (Cubical Agda)?
pathParam :: PureTCM m => Term -> m Bool
pathParam = \case
  Pi a b -> do
    here <- isJust <$> pathEnds (unEl (unDom a))
    if here then return True else pathParam (unEl (unAbs b))
  _ -> return False

-- | The goal through a continuation, see "Goals with continuations".
--   Returns the goal, the shape of the answer, and the signatures of the
--   local variables.
contGoal
  :: [(MetaId, Type)]  -- ^ The metas, with their closed types, in order.
  -> Type              -- ^ The rest of the type of the goal.
  -> Int               -- ^ The number of binders of @Δ@ coming from a path of functions.
  -> [String]          -- ^ Bound names.
  -> [CDecl]           -- ^ Binders of @Δ@ already met, the most recent first.
  -> Locals
  -> TransM (CDecl, Cont, Locals)
contGoal ms t swaps names delta locals = do
  t' <- instantiateFull t
  ends <- pathEnds (unEl t')
  -- A path of functions is a function to paths: its binders go to @Δ@.
  commuted <- if not (isPi (unEl t')) && isJust ends then commutePath (unEl t')
              else return Nothing
  case (commuted, unEl t') of
    (Just u, _) -> contGoal ms (t' { unEl = u }) (swaps + 1) names delta locals
    (_, Pi a b) | swaps > 0 || noMetas (unDom a) -> do
      (x, names') <- piBinder b names
      -- The binder is declared in the context, as the variables
      -- introduced by Agda: the equations of a parameter are only
      -- constraints on its instances, so the boundary of a path would not
      -- be a rewrite rule.
      (d, locals') <- declare Definition (unEl (unDom a)) x [] names locals
      pushDecl d
      contGoal ms (unAbs b) swaps names' (d : delta) locals'
    _ -> do
      -- The metas, as variables of their closed types.
      msigs <- forM ms $ \ (m, a) -> (,) (metaVarName m) . termSig <$> inlinePaths (unEl a)
      let locals' = foldr (\ (k, sg) -> Map.insert k (sg, Nothing)) locals msigs
      mdecls <- forM ms $ \ (m, a) -> fst <$> declare Parameter (unEl a) (metaVarName m) [] [] locals'
      let useS = isNothing ends
      final <- if useS then do
          -- @S ≡ B@, @b : S@.
          eb <- toCExpr (unEl t') names locals'
          lv <- sortLevel (getSort t')
          el <- toCExpr lv names locals'
          s  <- freshString "S"
          v  <- freshString "s"
          return [ CDecl s (Just (CExpr [] [] (CSpine "Type" [el])))
                           [CEquation (simpleSpine s) (spine eb) True]
                 , typed v (simpleExpr s) ]
        else do
          -- @g : B@, with the boundary of @B@, a path.
          g <- freshString "g"
          (gd, _) <- declare Parameter (unEl t') g [] names locals'
          return [gd]
      goal <- continuation (mdecls ++ final)
      let cont = Cont { contOuter = map name (reverse delta), contMetas = map fst ms
                      , contTyped = useS, contSwap = swaps }
      return (goal, cont, locals')

-- | Declares the interval, and returns the names of @i0@ and @i1@.
intervalEnds :: TransM (String, String)
intervalEnds = do
  iq  <- fromMaybe __IMPOSSIBLE__ <$> getBuiltinName' builtinInterval
  i0q <- fromMaybe __IMPOSSIBLE__ <$> getBuiltinName' builtinIZero
  i1q <- fromMaybe __IMPOSSIBLE__ <$> getBuiltinName' builtinIOne
  declareDef iq
  (,) <$> declaredName i0q <*> declaredName i1q

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

-- | The local variables: their signatures, and the type of the ones bound
--   by a λ whose binder is a function as a term (see 'toCExprAt'), with the
--   number of variables bound where this type was met.
type Locals = Map String (Sig, Maybe (Int, Type))

-- | A local variable, under @n@ bound variables: both signatures agree.
localSym :: Int -> (Sig, Maybe (Int, Type)) -> Sym
localSym n (s, mt) = Sym s ((\ (d, ty) -> raise (n - d) ty) <$> mt) s

-- | The name of a non-dependent binder: the one written by the user
--   (@(p : x ≡ y) → …@), or @a@ for an anonymous one (@A → B@).
anonName :: ArgName -> String
anonName n
  | null n || n == "_" = "a"
  | otherwise          = n

-- | A fresh name for the binder of a Π-type, and the bound names under it
--   (which only include a dependent binder).
piBinder :: Abs a -> [String] -> TransM (String, [String])
piBinder b names = case b of
  NoAbs n _ -> (, names) <$> freshString (anonName n)
  Abs n _   -> (\ x -> (x, x : names)) <$> freshString n

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
declarePi :: TransM ()
declarePi = do
  done <- seenMember "Pi" <$> getSeen
  unless done $ do
    lq <- fromMaybe __IMPOSSIBLE__ <$> getName' BuiltinLevel
    mq <- fromMaybe __IMPOSSIBLE__ <$> getName' PrimLevelMax
    modifySeen $ \ s -> foldr (uncurry seenInsert) s piSigs
    mapM_ declareDef [lq, mq]
    pushDecls piDecls

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
sortLevel :: HasBuiltins m => Sort -> m Term
sortLevel (Type l) = reallyUnLevelView l
sortLevel (SSet l) = reallyUnLevelView l
sortLevel _        = return (Level (Max 0 []))

-- | Translates the components of a Π-type @(x : A) → B@.
piParts :: Dom Type -> Abs Type -> [String] -> Locals -> TransM PiP
piParts a b names locals = do
  (x, names') <- case b of
    NoAbs _ _ -> (, names) <$> freshString "a"
    Abs n _   -> (\ x -> (x, x : names)) <$> freshString n
  lu <- sortLevel (getSort (unDom a))
  lv <- sortLevel (getSort (unAbs b))
  eu <- toCExpr lu names  locals
  ev <- toCExpr lv names' locals
  ea <- toCExpr (unEl $ unDom a) names locals
  let locals' = Map.insert x (termSig (unEl $ unDom a), Nothing) locals
  eb <- toCExprAt Nothing (unEl $ unAbs b) names' [untyped x] locals'
  declarePi
  return (PiP eu ev ea eb)

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
fixArg :: [String] -> Int -> Maybe Term -> CExpr -> Locals -> TransM CExpr
fixArg names k mty ce@(CExpr ps ls sp) locals
  | m == k = return ce
  | m < k  = etaExtend (k - m) ce
  | otherwise =
      case mty >>= stripPi (map name outer) names of
        Just (names', Pi dom b) -> do
          pp     <- piParts dom b names' locals
          inner' <- fixArg names' 1 (Just (Pi dom b)) (CExpr inner [] sp) locals
          return $ CExpr outer ls (CSpine "Pi.mk" (piArgs pp ++ [inner']))
        _ -> return ce
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
  -> Locals
  -> TransM (CSpine, [CDecl])
       -- ^ The spine, and the binders added by η-expansion.
applyHead hd Nothing _ cargs _ _ = return (CSpine hd cargs, [])
applyHead hd (Just Sym { symSig = sg, symTy = mty }) terms cargs names locals = do
  let ar   = length sg
      n    = length cargs
      ftys = maybe [] (`fnTypes` terms) mty
      expected i = case drop i ftys of
        (t : _) | Pi dom _ <- unEl t -> Just (unEl (unDom dom))
        _                            -> Nothing
      -- An argument beyond the signature, applied with @Pi.f@.
      extraArg g (i, ce) = case drop i ftys of
        (t : _) | Pi dom b <- unEl t -> do
          let dty = unEl (unDom dom)
          pp  <- piParts dom b names locals
          ce' <- fixArg names (arityOf dty) (Just dty) ce locals
          return $ CSpine "Pi.f" (piArgs pp ++ [CExpr [] [] g, ce'])
        _ -> return $ appendArg g ce
  fixed <- sequence [ fixArg names k (expected i) ce locals
                    | (i, k, ce) <- zip3 [0 ..] (map pArity sg) cargs ]
  xs    <- replicateM (max 0 (ar - n)) (freshString "x")
  etas  <- zipWithM etaVar xs (map pArity (drop n sg))
  sp    <- foldM extraArg (CSpine hd (fixed ++ etas)) (zip [ar ..] (drop ar cargs))
  return (sp, map untyped xs)
  where
    appendArg (CSpine h as) ce = CSpine h (as ++ [ce])

---------------------------------------------------------------------------
-- * Terms
---------------------------------------------------------------------------

-- | The role of a declaration, which decides what the equations of its
--   path boundary are.
data DeclKind
  = Parameter
      -- ^ A parameter: its equations are constraints on its instances.
  | Definition
      -- ^ A declaration of the context: its equations are rewrite rules.
  deriving Eq

-- | Translates a type into a declaration, and records its signature.
--
--   In Cubical Agda, the path types in type positions become functions of
--   the interval; if the type is a path type @PathP A x y@, its boundary
--   @n i0 ≡ x@, @n i1 ≡ y@ is added to the equations (see 'pathEquations').
declare
  :: DeclKind
  -> Term            -- ^ The type of the declaration.
  -> String          -- ^ Its name.
  -> [CEquation]     -- ^ Its equations.
  -> [String]        -- ^ Bound names.
  -> Locals
  -> TransM (CDecl, Locals)
declare kind t0 n eqs names locals = do
  t    <- lift $ unfoldPis =<< inlinePaths t0
  ty   <- toCType t names locals
  peqs <- pathEquations kind n ty t0 names locals
  return (CDecl n (Just ty) (eqs ++ peqs), Map.insert n (termSig t, Nothing) locals)

-- | Unfolds the definitions that stand for Π-types (@X = (P : Set₁) → (A → P) → P@)
--   in the type of a declaration, so that its binders are parameters.  The
--   other definitions are not unfolded.
unfoldPis :: Term -> TCM Term
unfoldPis t = do
  t' <- reduce t `catchError` \ _ -> return t
  case t' of
    Pi a b -> do
      b' <- traverse (\ (El s u) -> El s <$> unfoldPis u) b
      return (Pi a b')
    _ -> return t

-- | The boundary of a declaration @n : Δ → PathP A x y@, translated as
--   @n : Δ → (i : I) → A i@ with the type @ty@:
--
--   > n δ i0 ⤇ x        n δ i1 ⤇ y
--
--   η-expanded if @A@ is a function type.  As constraints (for a
--   'Parameter'), these equations cannot bind variables: they are only
--   given when @Δ@ and the arguments of @A@ are empty.
pathEquations :: DeclKind -> String -> CExpr -> Term -> [String] -> Locals -> TransM [CEquation]
pathEquations kind n ty t0 names locals = pathEnds t0 >>= \case
  Just (k, x, y) | length (params ty) > k -> do
    (i0, i1) <- intervalEnds
    let outer  = map name (take k (params ty))
        extra  = length (params ty) - k - 1
        names' = reverse outer ++ names
        end i u = do
          eu <- etaTo extra =<< toCExpr u names' locals
          let xs  = map name (params eu)
              lhs = CSpine n (map simpleExpr (outer ++ [i] ++ xs))
              ok  = length xs == extra && (kind == Definition || (k == 0 && extra == 0))
          return [ CEquation lhs (spine eu) True | ok ]
    concat <$> zipWithM end [i0, i1] [x, y]
  _ -> return []

-- | Translates a type: its Π-binders become parameters.
toCType :: Term -> [String] -> Locals -> TransM CExpr
toCType = go []
  where
    go ps (Pi a b) names locals = do
      (x, names') <- piBinder b names
      (d, locals') <- declare Parameter (unEl $ unDom a) x [] names locals
      go (d : ps) (unEl $ unAbs b) names' locals'
    go ps t names locals = toCExprAt Nothing t names ps locals

-- | Translates a term.  A Π-type is encoded with @Pi@; λ-binders become
--   parameters.
toCExpr :: Term -> [String] -> Locals -> TransM CExpr
toCExpr t names = toCExprAt Nothing t names []

-- | 'toCExpr' under the given parameters (the most recent first), given the
--   type expected for the term if known, both as declared and as
--   instantiated (e.g. @(a : X) → Set@ and @(a : X → X) → Set@ for the
--   second argument of @Σ-i@ at @X := X → X@).  A λ-binder whose declared
--   type is not a Π-type but whose instantiated type is one is a function
--   as a term (@Pi u v A B@): its applications go through @Pi.f@, and its
--   type is recorded for that.
toCExprAt :: Maybe (Type, Type) -> Term -> [String] -> [CDecl] -> Locals -> TransM CExpr
toCExprAt ex t names ps locals = case t of
  Pi a b -> do
    pp <- piParts a b names locals
    return $ CExpr (reverse ps) [] (CSpine "Pi" (piArgs pp))
  Lam _ b -> do
    -- A fresh name, which cannot capture a variable of the context (the
    -- binder @p@ of a constraint would capture the path @p@).
    (names', x) <- case b of
      NoAbs _ _ -> return (names, "_")
      Abs y _   -> (\ x -> (x : names, x)) <$> freshString y
    (ex', bty, locals') <- lamBinder ex x b names locals
    toCExprAt ex' (unAbs b) names' (CDecl x bty [] : ps) locals'
  _ -> do
    (sp, extra) <- toCSpine t names locals
    return $ CExpr (reverse ps ++ extra) [] sp

-- | The binder of a λ whose type is expected to be @ex@ (see 'toCExprAt'):
--   the type expected for its body, the type of the binder if it is a
--   function as a term, and the local variables under it.  @x@ is the name
--   given to the binder.
lamBinder :: Maybe (Type, Type) -> String -> Abs Term -> [String] -> Locals
          -> TransM (Maybe (Type, Type), Maybe CExpr, Locals)
lamBinder Nothing _ _ _ locals = return (Nothing, Nothing, locals)
lamBinder (Just (raw, inst)) x b names locals = do
  r <- reduce (unEl raw)
  i <- reduce (unEl inst)
  case (r, i) of
    (Pi rd rb, Pi idom ib) -> do
      bt <- reduce (unEl (unDom idom))
      let next = Just (absBody rb, absBody ib)
      if isPi (unEl (unDom rd)) || not (isPi bt) then return (next, Nothing, locals) else do
        -- The type of a function as a term is given to the binder.
        e <- toCExpr bt names locals
        let locals' = case b of
              Abs{}   -> Map.insert x ([], Just (length names, El (getSort (unDom idom)) bt)) locals
              NoAbs{} -> locals
        return (next, Just e, locals')
    _ -> return (Nothing, Nothing, locals)

-- | Translates a neutral term or a sort.
--
--   Returns the binders added by η-expansion (see 'applyHead').
--   Unsupported terms are opaque constants, named by their printed form.
toCSpine :: Term -> [String] -> Locals -> TransM (CSpine, [CDecl])
toCSpine t names locals = case t of
  Var i es -> localApp (names !! i) es
  MetaV m es
    -- A meta of the goal (see "Goals with metas"), applied to its context.
    | Map.member (metaVarName m) locals -> localApp (metaVarName m) es
    | otherwise -> foreignMeta m es
  Sort (MetaS m es) -> foreignMeta m es
  Sort (Type l) -> universe "Type" l
  Sort (SSet l) -> universe "ß" l
  Sort IntervalUniv -> return (simpleSpine "IUniv", [])
  Level l -> do
    t' <- reallyUnLevelView l
    toCSpine t' names locals
  Def q es -> do
    sym <- lift $ globalSym q
    def <- lift $ constInfo q
    -- A constructor applied to the parameters of its datatype (see
    -- "Agda.Canonical.Params").
    sym' <- case theDef def of
      ConstructorDefn{} -> do
        ty <- lift $ restoredType def
        return sym { symSig = symDecl sym, symTy = Just ty }
      _ -> return sym
    let exps = maybe [] (\ ty -> argTypes ty ty (appliedTerms es)) (symTy sym')
    as <- elimsToCExprAt exps es names locals
    declareDef q
    hd <- declaredName q
    applyHead hd (Just sym') (appliedTerms es) as names locals
  Con c _ es -> do
    dataname <- getConstInfo (conName c) <&> \ d -> case theDef d of
      ConstructorDefn cd -> _conData cd
      _                  -> __IMPOSSIBLE__
    as <- elimsToCExpr es names locals
    declareDef dataname
    sym <- lift $ globalSym (conName c)
    hd  <- declaredName (conName c)
    applyHead hd (Just sym) (appliedTerms es) as names locals
  Lit l -> do
    -- A natural number is unfolded into @suc (… zero)@, one constructor
    -- at a time, so that the clauses on @zero@ and @suc@ compute on it.
    mz <- getBuiltin' builtinZero
    ms <- getBuiltin' builtinSuc
    case (l, constructorForm' mz ms t) of
      (LitNat n, Just t') | n <= maxUnaryNat -> toCSpine t' names locals
      _ -> literalConst l names
  _ -> (, []) <$> opaque (P.prettyShow t)
  where
    foreignMeta m es = do
      sym <- declareMeta m
      as  <- elimsToCExpr es names locals
      applyHead (metaVarName m) sym (appliedTerms es) as names locals
    localApp h es = do
      as <- elimsToCExpr es names locals
      applyHead h (localSym (length names) <$> Map.lookup h locals) (appliedTerms es) as names locals
    universe h l = do
      lv <- reallyUnLevelView l
      a  <- toCExpr lv names locals
      return (CSpine h [a], [])

-- | An opaque constant without type, declared if it is not yet.
opaque :: String -> TransM CSpine
opaque x = do
  done <- seenMember x <$> getSeen
  unless done $ do
    modifySeen (seenInsert x [])
    pushDecl (untyped x)
  return (simpleSpine x)

-- | Declares a meta that is not one of the goal, e.g. the type @?A@ of a
--   variable of the context @{a : ?A}@, as an opaque constant of its closed
--   type (Canonical cannot find it), or without type if it is not known.
--   Returns its signatures.
declareMeta :: MetaId -> TransM (Maybe Sym)
declareMeta m = do
  mty <- lift $ closedMetaType m
  msym <- lift $ forM mty $ \ a -> do
    sg <- tySig a
    return Sym { symSig = sg, symTy = Just a, symDecl = sg }
  done <- seenMember x <$> getSeen
  unless done $ do
    -- Declared before its type, which may mention it.
    modifySeen (seenInsert x (maybe [] symDecl msym))
    case mty of
      Just a  -> pushDecl . fst =<< declare Definition (unEl a) x [] [] Map.empty
      Nothing -> pushDecl (untyped x)
  return msym
  where
    x = metaVarName m

-- | The largest natural number literal unfolded into constructors; the
--   larger ones are opaque constants (see 'literalConst').
maxUnaryNat :: Integer
maxUnaryNat = 1000

-- | A literal that is not unfolded into constructors (a string, a
--   character, …) is declared as an opaque constant of its type, named by
--   its printed form.  It is kept undeclared if its type is unknown.
literalConst :: Literal -> [String] -> TransM (CSpine, [CDecl])
literalConst l names = do
  done <- seenMember s <$> getSeen
  unless done $ do
    mty <- lift $ (Just <$> litType l) `catchError` \ _ -> return Nothing
    whenJust mty $ \ ty -> do
      modifySeen (seenInsert s [])
      (d, _) <- declare Definition (unEl ty) s [] names Map.empty
      pushDecl d
  return (simpleSpine s, [])
  where
    s = P.prettyShow l

-- | Translates the arguments of a list of eliminations.
--
--   The application of a path to an interval term is an ordinary application
--   (see "Agda.Canonical.Cubical").  Projections are not supported; they are
--   opaque constants, named by their printed form.
elimsToCExpr :: [Elim' Term] -> [String] -> Locals -> TransM [CExpr]
elimsToCExpr = elimsToCExprAt []

-- | 'elimsToCExpr', given the types expected for the applied terms, as
--   declared and as instantiated (see 'toCExprAt' and 'argTypes').
elimsToCExprAt :: [Maybe (Type, Type)] -> [Elim' Term] -> [String] -> Locals -> TransM [CExpr]
elimsToCExprAt exps es names locals = zipWithM elim (snd (mapAccumL expect exps es)) es
  where
    -- Each applied term takes the next expected type.
    expect xs Proj{}   = (xs, Nothing)
    expect (x : xs) _  = (xs, x)
    expect []       _  = ([], Nothing)
    elim ex = \case
      Apply a      -> toCExprAt ex (unArg a) names [] locals
      IApply _ _ r -> toCExpr r names locals
      e            -> CExpr [] [] <$> opaque (P.prettyShow e)

-- | The types of the arguments of a function of type @raw@, as declared
--   (the earlier arguments are variables) and as instantiated with the
--   given arguments (in @inst@).
argTypes :: Type -> Type -> [Term] -> [Maybe (Type, Type)]
argTypes raw inst (a : as)
  | Pi rd rb <- unEl raw, Pi idom ib <- unEl inst =
      Just (unDom rd, unDom idom) : argTypes (absBody rb) (absApp ib a) as
argTypes _ _ _ = []

-- | Is the term a Π-type?
isPi :: Term -> Bool
isPi Pi{} = True
isPi _    = False

---------------------------------------------------------------------------
-- * Definitions
---------------------------------------------------------------------------

-- | Declares a definition (and what it depends on) to Canonical, if not
--   done yet.  The types of definitions are closed.
--
--   * A datatype comes with its constructors and its recursor.
--   * A record comes with its constructor and its projections.
--   * A function comes with its clauses, as rewrite rules.
--   * @_⊔_@ comes with 'levelMaxEqs', and @PathP@ with @Path.mk@ and @Path.f@.
declareDef :: QName -> TransM ()
declareDef q = do
  done <- Map.member q . seenCanon <$> getSeen
  unless done $ do
    def <- lift $ constInfo q
    case theDef def of
      -- A constructor is declared with its datatype.
      ConstructorDefn cd -> declareDef (_conData cd)
      _ -> do
        n   <- pickName q
        sym <- lift $ globalSym q
        dty <- lift $ restoredType def
        modifySeen (seenInsertDef n q (symDecl sym))
        eqs <- builtinEqs q n
        (d, _) <- declare Definition (unEl dty) n eqs [] Map.empty
        declareBody q def sym d

-- | Declares a definition, given the declaration of its type, with what
--   comes with it (see 'declareDef').
declareBody :: QName -> Definition -> Sym -> CDecl -> TransM ()
declareBody q def sym d = case theDef def of
  DatatypeDefn dd -> do
    pushDecl d
    ctors <- declareCtors (_dataCons dd)
    -- The interval cannot be eliminated.
    interval <- isInterval q
    mrec <- if interval then return Nothing else lift $ mkRecursor (_dataPars dd) d ctors
    pushDecls ctors
    declareRecursor mrec
  RecordDefn rd -> do
    pushDecl d
    ctors <- declareCtors [conName (_recConHead rd)]
    pushDecls ctors
    -- The projections, whose rules mention the constructor.
    mapM_ (declareDef . unDom) (_recFields rd)
    -- With η-equality, the projections are enough (Agda identifies @r@
    -- and @c (r .f₁) … (r .fₙ)@), and give simpler solutions than a
    -- pattern-matching λ.  Otherwise, the recursor is printed as a
    -- pattern-matching λ on the constructor, which needs a name.  A
    -- coinductive record (e.g. @∞@, @BUILTIN INFINITY@) cannot be
    -- matched on.
    let eta   = case _recEtaEquality rd of { YesEta -> True; _ -> False }
        coind = _recInduction rd == Just CoInductive
    mrec <- if _recNamedCon rd && not eta && not coind
            then lift $ mkRecursor (_recPars rd) d ctors else return Nothing
    declareRecursor mrec
  -- As in Agda, a function that fails the termination check, or an
  -- irrelevant one, is not unfolded: it has no rules.
  FunctionDefn fd -> do
    let cls | defNonterminating def || isIrrelevant def = []
            | otherwise                                 = _funClauses fd
    withClauses (droppedParams (theDef def)) cls
  -- A builtin function on natural numbers (@BUILTIN NATPLUS@, …) keeps
  -- its clauses, which Agda uses on terms that are not literals.
  PrimitiveDefn pd | not (null (_primClauses pd)) -> withClauses 0 (_primClauses pd)
  _ -> do
    pushDecl d
    -- @PathP@ comes with @Path.mk@ and @Path.f@.
    pathP <- (Just q ==) <$> getBuiltinName' builtinPathP
    cub   <- isCubical
    when (pathP && cub) $ do
      iq <- fromMaybe __IMPOSSIBLE__ <$> getBuiltinName' builtinInterval
      (i0, i1) <- intervalEnds
      iN <- declaredName iq
      pushDecls (pathDecls (name d) iN i0 i1)
      modifySeen $ \ s -> foldr (uncurry seenInsert) s pathSigs
  where
    withClauses np cls = do
      eqs <- clausesToEquations q (symDecl sym) np cls
      pushDecl d { equations = equations d ++ eqs }
    declareRecursor = flip whenJust $ \ (r, s) -> do
      pushDecl r
      modifySeen (seenInsert (name r) s)

-- | Declares constructors, and @Level@ (for the recursor).  Returns their
--   declarations, in order, which are not added to the context yet.
declareCtors :: [QName] -> TransM [CDecl]
declareCtors cs = do
  syms <- lift $ mapM globalSym cs
  tys  <- lift $ mapM (restoredType <=< constInfo) cs
  ns   <- forM (zip cs syms) $ \ (c, s) -> do
    n <- pickName c
    modifySeen (seenInsertDef n c (symDecl s))
    return n
  ds <- forM (zip tys ns) $ \ (t, n) -> fst <$> declare Definition (unEl t) n [] [] Map.empty
  declareDef =<< fromMaybe __IMPOSSIBLE__ <$> getName' BuiltinLevel
  return ds

-- | The names of the declarations of "Agda.Canonical.Builtin", and of the
--   symbols of Agda that they, or the rules of 'builtinEqs', mention.
reservedNames :: [String]
reservedNames =
  [ "Type", "ß", "IUniv", "Pi", "Pi.mk", "Pi.f", "Path.mk", "Path.f", "Goal"
  , "Level", "lzero", "lsuc", "_⊔_", "primIMin", "primIMax", "primINeg" ]

-- | The reserved name of a symbol of Agda that "Agda.Canonical.Builtin"
--   mentions, whatever its name in Agda.
fixedName :: HasBuiltins m => QName -> m (Maybe String)
fixedName q = do
  lv <- getName' BuiltinLevel
  lz <- getName' builtinLevelZero
  ls <- getName' builtinLevelSuc
  mx <- getName' PrimLevelMax
  ps <- mapM getPrimitiveName' [PrimIMin, PrimIMax, PrimINeg]
  return $ lookup (Just q) $
    zip [lv, lz, ls, mx] ["Level", "lzero", "lsuc", "_⊔_"] ++
    zip ps ["primIMin", "primIMax", "primINeg"]

-- | The name to declare a definition under: 'symName', with primes if it is
--   already taken (Agda names may be overloaded) or reserved.  It is
--   recorded by 'seenInsertDef'.
pickName :: QName -> TransM String
pickName q = fixedName q >>= \case
  Just n  -> return n
  Nothing -> do
    base <- symName q
    seen <- getSeen
    -- A name ending in @.rec@ (a field @rec@) would be taken for a recursor.
    let taken n = n `seenMember` seen || n `elem` reservedNames || ".rec" `isSuffixOf` n
    return $ until (not . taken) (++ "'") base

-- | The name under which a definition is declared ('pickName'); 'symName'
--   if it is not declared.
declaredName :: QName -> TransM String
declaredName q = maybe (symName q) return . Map.lookup q . seenCanon =<< getSeen

-- | The name of a definition in Agda, as declared to Canonical when it is
--   free: its unqualified name, except for a record projection, qualified
--   by its record (@R.f@), since field names are often also names of
--   variables.
symName :: HasConstInfo m => QName -> m String
symName q = getConstInfo q <&> \ d -> case theDef d of
  Function { funProjection = Right p } | Just r <- projProper p ->
    nameToString r ++ "." ++ nameToString q
  _ -> nameToString q

-- | The type of a definition, with the parameters left out by Agda put back
--   (see "Agda.Canonical.Params").
restoredType :: Definition -> TCM Type
restoredType def = inTopContext $ restoreType (defType def)

-- | The rules of a symbol that Agda computes with internally: @_⊔_@ on
--   levels, and the primitives on the interval in Cubical Agda.
builtinEqs :: QName -> String -> TransM [CEquation]
builtinEqs q n = fixedName q >>= \case
  Just "_⊔_" -> return levelMaxEqs
  Just p | p `elem` ["primIMin", "primIMax", "primINeg"] -> do
    cub <- isCubical
    if not cub then return [] else do
      (i0, i1) <- intervalEnds
      return (intervalEqs i0 i1 n)
  _ -> return []

-- ** Clauses

-- | Translates the clauses of a function, skipping the unsupported ones.
--
--   Agda tries the clauses in order, while Canonical's rewrite rules may
--   apply in any order: each clause only stands for the instances of its
--   patterns that no earlier clause matches (see 'disjoint').  With
--   @f 1 = 7@ and @f (suc n) = n@, the second rule is @f (suc (suc y)) ⤇ suc y@.
clausesToEquations :: QName -> Sig -> Int -> [Clause] -> TransM [CEquation]
clausesToEquations q sg np cls = do
  lhss <- lift $ mapM (clauseLhs np) cls
  fmap concat $ forM (zip [0 ..] lhss) $ \ (i, (cl, ns, mps)) -> case mps of
    Nothing -> return []
    Just ps -> do
      -- An absurd clause, or one without rule, still comes first.
      pieces <- lift $ disjoint ps [ qs | (_, _, Just qs) <- take i lhss, length qs == length ps ]
      fromMaybe [] <$> attempt (clauseToEquations q sg np cl ns pieces)

-- | The patterns of a clause, preceded by wildcards for the parameters
--   dropped by Agda from the clauses of a projection or of a
--   projection-like function (see "Agda.Canonical.Params"): its body does
--   not use them.  Also returns the fresh names of the variables of the
--   clause, the first one first.  'Nothing' for an unsupported pattern.
clauseLhs :: Int -> Clause -> TCM (Clause, [String], Maybe [Pat])
clauseLhs np cl = do
  ns  <- mapM freshString (teleNames (clauseTel cl))
  ws  <- replicateM np (LVar <$> freshString "p")
  mps <- mapM (patToPat (reverse ns) . namedArg) (namedClausePats cl)
  return (cl, ns, (ws ++) <$> sequence mps)

-- | Translates a clause into rewrite rules, in η-long form: one for each
--   instance of its patterns given by 'disjoint', with its substitution
--   applied to the body.
--
--   The clause is skipped (no rule) if it has no body or more patterns than
--   the signature, or if its body contains an unsolved meta or uses a
--   function that the user cannot write (see 'isAuxiliary').
clauseToEquations :: QName -> Sig -> Int -> Clause -> [String] -> [([Pat], Map String Pat)]
                  -> MaybeT TransM [CEquation]
clauseToEquations q sg np cl ns pieces = do
  -- A body that is still a hole, or contains one, is not a definition yet.
  body0 <- MaybeT $ return (clauseBody cl)
  body1 <- instantiateFull body0
  aux   <- lift $ anyM isAuxiliary (namesIn body1 :: [QName])
  let tel = clauseTel cl
      ar  = length sg
      n   = np + length (namedClausePats cl)
  guard (not aux && noMetas body1 && n <= ar)
  body <- liftTCM $ inTopContext $ addContext tel $ restoreTerm (unArg <$> clauseType cl) body1
  sigs <- mapM (fmap termSig . inlinePaths . unEl . snd . unDom) (telToList tel)
  let locals = Map.fromList (zip ns (map (, Nothing) sigs))
  -- @Var i@ is the name at position @i@.
  (xs, names, b) <- peel (ar - n) (reverse ns) body
  e <- lift $ toCExpr b names locals
  let k = ar - n - length xs
      j = length (params e)
  guard (j <= k)
  e' <- etaExtend (k - j) e
  f  <- lift $ declaredName q
  -- The constructors of the patterns, declared with their datatypes.
  let ctors = concat [ patCtors p | (ps, sub) <- pieces, p <- ps ++ Map.elems sub ]
  lift $ mapM_ declareDef ctors
  cnames <- Map.fromList <$> mapM (\ c -> (c,) <$> lift (declaredName c)) ctors
  let pe    = patExpr (\ c -> Map.findWithDefault (nameToString c) c cnames)
      extra = map simpleExpr (xs ++ map name (params e'))
  forM pieces $ \ (ps, sub) -> do
    l <- zipWithM etaTo (map pArity sg) (map pe ps)
    let rhs = substExpr (Map.map pe sub) e'
    return (CEquation (CSpine f (l ++ extra)) (spine rhs) True)

-- *** Disjoint clauses

-- | A pattern of a left-hand side: a variable (or a wildcard), or a
--   constructor applied to the parameters of its datatype (wildcards) and to
--   its fields.
data Pat = LVar String | LCon QName [Pat]

-- | A pattern as an argument of a left-hand side, given the names of the
--   constructors.
patExpr :: (QName -> String) -> Pat -> CExpr
patExpr _ (LVar x)     = simpleExpr x
patExpr nm (LCon c ps) = CExpr [] [] (CSpine (nm c) (map (patExpr nm) ps))

-- | The constructors of a pattern.
patCtors :: Pat -> [QName]
patCtors (LVar _)    = []
patCtors (LCon c ps) = c : concatMap patCtors ps

-- | Substitution of patterns for variables in a pattern.
substPat :: Map String Pat -> Pat -> Pat
substPat sub p@(LVar x) = Map.findWithDefault p x sub
substPat sub (LCon c ps) = LCon c (map (substPat sub) ps)

-- | Substitution of (first-order) expressions for variables in an
--   expression; the names are fresh, so there is no capture.
substExpr :: Map String CExpr -> CExpr -> CExpr
substExpr sub (CExpr ps ls (CSpine h as)) =
  CExpr (map substD ps) (map substD ls) $ case Map.lookup h sub of
    Just (CExpr [] _ (CSpine h' bs)) -> CSpine h' (bs ++ as')
    _                                -> CSpine h as'
  where
    as'      = map (substExpr sub) as
    substD d = d { typ = substExpr sub <$> typ d }

-- | The most instances of a clause with more than this many rules, which
--   is then kept as it is.
maxPieces :: Int
maxPieces = 64

-- | @disjoint ps qss@: the instances of the patterns @ps@ that are not
--   instances of the earlier clauses @qss@, as disjoint lists of patterns,
--   each one with the substitution of the variables of @ps@ that gives it.
--   If there are too many of them ('maxPieces'), the clause is kept as it is.
disjoint :: [Pat] -> [[Pat]] -> TCM [([Pat], Map String Pat)]
disjoint ps0 qss = go [(ps0, Map.empty)] qss
  where
    go acc [] = return acc
    go acc (qs : rest) = do
      acc' <- concat <$> mapM (\ (ps, s) -> map (compose s) <$> minus ps qs) acc
      if length acc' > maxPieces then return [(ps0, Map.empty)] else go acc' rest

-- | @compose s (ps, s')@ applies @s'@ after @s@.
compose :: Map String Pat -> ([Pat], Map String Pat) -> ([Pat], Map String Pat)
compose s (ps, s') = (ps, Map.union (Map.map (substPat s') s) s')

-- | @minus ps qs@: the instances of @ps@ that are not instances of @qs@.  If
--   they clash (different constructors at the same position), all of them;
--   if @qs@ is more general, none; otherwise a variable of @ps@ facing a
--   constructor of @qs@ is replaced by each constructor of its datatype, and
--   so on.
minus :: [Pat] -> [Pat] -> TCM [([Pat], Map String Pat)]
minus ps qs
  | or (zipWith clash ps qs) = return [(ps, Map.empty)]
  | otherwise = case firstJust (zipWith splitAt' ps qs) of
      Nothing     -> return []
      Just (x, d) -> do
        cs <- siblingCtors d
        concat <$> forM cs (\ (c, k) -> do
          ys <- replicateM k (LVar <$> freshString "y")
          let s = Map.singleton x (LCon c ys)
          map (compose s) <$> minus (map (substPat s) ps) qs)
  where
    clash (LCon c as) (LCon d bs) = c /= d || or (zipWith clash as bs)
    clash _ _                     = False
    splitAt' (LVar x) (LCon d _)    = Just (x, d)
    splitAt' (LCon _ as) (LCon _ bs) = firstJust (zipWith splitAt' as bs)
    splitAt' _ _                     = Nothing
    firstJust = listToMaybe . catMaybes

-- | The constructors of the datatype of a constructor, with their numbers
--   of arguments (parameters included).
siblingCtors :: QName -> TCM [(QName, Int)]
siblingCtors q = do
  d <- theDef <$> getConstInfo q
  cons <- case d of
    ConstructorDefn cd -> theDef <$> getConstInfo (_conData cd) <&> \case
      DatatypeDefn dd -> _dataCons dd
      RecordDefn rd   -> [conName (_recConHead rd)]
      _               -> [q]
    _ -> return [q]
  forM cons $ \ c -> theDef <$> getConstInfo c <&> \case
    ConstructorDefn cd -> (c, _conPars cd + _conArity cd)
    _                  -> __IMPOSSIBLE__

-- | A pattern-matching lambda or the auxiliary function of a @with@: their
--   names cannot be written in Agda, so a solution must not unfold to them.
isAuxiliary :: QName -> TransM Bool
isAuxiliary q = getConstInfo q <&> \ d -> case theDef d of
  Function { funExtLam = Just _ } -> True
  Function { funWith = WithFunction{} } -> True
  _                               -> False

-- | Translates a pattern into a pattern of a left-hand side.
--
--   A dot pattern becomes a fresh wildcard; the parameters of a constructor,
--   absent from Agda patterns, become fresh wildcards; an interval pattern
--   (@f p i = …@) is a variable; a natural number literal is unfolded into
--   @suc (… zero)@.  The other literals, projections and the other cubical
--   patterns are not supported ('Nothing').
patToPat :: [String] -> DeBruijnPattern -> TCM (Maybe Pat)
patToPat names p = case p of
  LitP _ (LitNat n) | n <= maxUnaryNat -> do
    mz <- getBuiltin' builtinZero
    ms <- getBuiltin' builtinSuc
    return $ case (mz, ms) of
      (Just (Con z _ _), Just (Con s _ _)) ->
        Just (iterate (LCon (conName s) . pure) (LCon (conName z) []) !! fromInteger n)
      _ -> Nothing
  VarP _ x -> return . Just $ LVar (names !! dbPatVarIndex x)
  IApplyP _ _ _ x -> return . Just $ LVar (names !! dbPatVarIndex x)
  DotP _ _ -> Just . LVar <$> freshString "w"
  ConP c _ ps -> do
    np   <- conParCount (conName c)
    ws   <- replicateM np (LVar <$> freshString "p")
    subs <- mapM (patToPat names . namedArg) ps
    return $ LCon (conName c) . (ws ++) <$> sequence subs
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
peel :: MonadFresh NameId m => Int -> [String] -> Term -> m ([String], [String], Term)
peel k ns (Lam _ b) | k > 0 = do
  x <- freshString (absName b)
  let ns' = case b of { Abs{} -> x : ns; NoAbs{} -> ns }
  (xs, ns'', t) <- peel (k - 1) ns' (unAbs b)
  return (x : xs, ns'', t)
peel _ ns t = return ([], ns, t)
