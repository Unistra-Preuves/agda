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
--     de Bruijn index @i@ is the name at position @i@.  The context of Agda
--     is extended with them ('underBinder'): the terms are translated as
--     Agda has them, and the parameters it leaves out are put back where
--     each subterm is translated, from the types (see "Agda.Canonical.Params");
--
--   * the signatures of the local variables ('Locals'), used to η-expand
--     their arguments.
--
--   Canonical has no universe-polymorphic Π-type: a Π-type occurring as a
--   term is encoded with @Pi@, @Pi.mk@ and @Pi.f@ (see "Agda.Canonical.Builtin").
--
--   This module builds the goal; the translation itself is split into
--
--   * "Agda.Canonical.ToCanonical.Monad": the monad, and the signatures of
--     the symbols;
--
--   * "Agda.Canonical.ToCanonical.Term": terms, types and definitions;
--
--   * "Agda.Canonical.ToCanonical.Pattern": the left-hand sides of the
--     rules given by clauses, and their disjoint instances.

module Agda.Canonical.ToCanonical
  ( produceCanonicalGoal
  , undeclaredSymbols
  , isIntervalType
  ) where

import Control.Monad (foldM, forM, when)
import Control.Monad.State (evalStateT, gets, lift)
import Data.List (nub)
import Data.Map qualified as Map
import Data.Maybe (catMaybes, isJust, isNothing, maybeToList)
import Data.Set (Set)
import Data.Set qualified as Set

import Agda.Canonical.Builtin
import Agda.Canonical.Cubical
import Agda.Canonical.ToCanonical.Monad
import Agda.Canonical.ToCanonical.Term
import Agda.Canonical.Types
import Agda.Canonical.Utils
import Agda.Syntax.Builtin
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty qualified as P
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Generic (foldTerm)
import Agda.Syntax.Internal.MetaVars (allMetasList, noMetas)
import Agda.TypeChecking.EtaContract (etaContract)
import Agda.TypeChecking.Free (Free, freeIn)
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Context (addContext, inTopContext)
import Agda.TypeChecking.Monad.Pure (PureTCM)
import Agda.TypeChecking.Monad.Signature (HasConstInfo (getConstInfo))
import Agda.TypeChecking.Reduce (instantiateFull, reduce)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope (telView, telViewUpTo, teleArgs)
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
produceCanonicalGoal lemmas ctx hyps ty bds (mv, cons) = do
  cub <- isCubical
  -- In Cubical Agda, the interval and its primitives are always available.
  prims <- if not cub then return [] else
    catMaybes <$> mapM getPrimitiveName' [PrimIMin, PrimIMax, PrimINeg]
  -- The empty system, when the problem has an empty face (see 'faceSymbols').
  empty <- if not cub then return [] else do
    e <- mentionsEmptyFace (unEl ty : concat [ [u, v] | (u, v) <- cons ])
    if e then maybeToList <$> getBuiltinName' builtinIsOneEmpty else return []
  let start = TransState
        { tsContext = [halfDecl | cub] ++ [typeDecl] ++ [iunivDecl | cub]
        , tsSeen    = seenFromList ([typeSig] ++ [ (n, []) | cub, n <- auxNames ])
        , tsNotes   = [] }
  -- The terms are translated as Agda has them, in their context (see
  -- 'Agda.Canonical.Params.restoreRoot'), from the top level.
  inTopContext $ flip evalStateT start $ do
    mapM_ declareDef (prims ++ lemmas ++ empty)
    -- When the constraints link the hole to other metas, which may depend
    -- on it in turn (e.g. the holes in the faces of an @hcomp@, whose
    -- boundaries mention each other), they are all found together: the
    -- boundary of the hole is then a constraint like the others, and the
    -- solution a function of the refolded variables (see
    -- 'constrainedGoal'), rather than a path whose binders could go to @Δ@.
    let joint = cub && any (\ c -> let xs = allMetasList c in mv `elem` xs && any (/= mv) xs) cons
    own <- if joint then lift (ownBoundary ctx mv bds) else return []
    let consJ = cons ++ own
    (ctx', ty', refolded) <- lift $
      refoldBoundary (constrainedVars (size ctx) mv consJ) ctx ty (if joint then [] else bds)
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
        -- (to none of them, e.g. @?1 = 3@ once @?0 + ?1 = 3@ is reduced).
        cut (u, v) = (,) <$> cutMeta (size ctx) m mv u <*> cutMeta (size ctx) m mv v
        -- A constraint that still mentions a refolded variable (@?80 j i1 =
        -- p j@, or @?0 i i1 = p (~ i)@ for the face @j = i1@ of a square)
        -- is abstracted over them, as an equation between functions: the
        -- refolded variables become its binders, the others are raised
        -- past them.
        lams t = teleLam (telFromList (drop (size ctx - m) (telToList ctx)))
                         (applySubst (liftS m (raiseS m)) t)
        cutCons = nub [ c | (u, v) <- consJ
                      , Just c <- [ case cut (u, v) of
                                      Nothing -> cut (lams u, lams v)
                                      r       -> r ] ]
    declareContext ctx' ty' [] Map.empty $ \ t names locals0 -> do
      locals <- foldM (declareHypothesis names) locals0 hyps'
      ms0     <- lift $ fromMaybe [] <$> goalMetas t
      -- The metas that the constraints link to the hole or to the metas of
      -- its type are found too (e.g. the other holes of an @hcomp@, whose
      -- boundaries mention each other): the constraints on all of them are
      -- kept, even when they depend on each other cyclically.
      ms      <- lift $ fromMaybe ms0 <$> linkedMetas mv ms0 cutCons
      let known = mv : map fst ms
          cons' = [ c | c <- cutCons, all (`elem` known) (allMetasList c) ]
      ends    <- pathEnds (unEl t)
      -- The first parameters stand for the refolded variables.
      sig     <- drop (length refolded) . termSig <$> inlinePaths (unEl t)
      -- The boundary of a parameter of path type is only a rewrite rule
      -- through a continuation, which declares it in the context.
      pathPar <- pathParam (unEl t)
      (goal, cont, locals') <- if
        | not (null cons'), joint || any ((mv `elem`) . allMetasList) cons' -> do
            (g, c, l) <- constrainedGoal mv cons' ms t names locals
            return (g, Just c, l)
        | null ms, isNothing ends, not pathPar -> do
            g <- directGoal t names locals
            return (g, Nothing, locals)
        | otherwise -> do
            (g, c, l) <- contGoal cons' ms t 0 names [] locals
            return (g, Just c, l)
      roots <- mapM declaredName lemmas
      goal  <- relevance roots goal
      seen  <- getSeen
      notes <- gets (nub . reverse . tsNotes)
      return (goal, emptyGoalInfo
        { giContext = maybe [] lets (typ goal)
        , giGlobals = seenSigs seen, giDefs = seenNames seen
        , giLocals  = Map.insert "Goal" sig (Map.map fst locals')
        , giNames   = reverse refolded ++ names
        , giCont    = cont
        , giRefold  = refolded
        , giNotes   = notes })

-- | Which definitions of the context are candidates of the search, as in
--   the translation of Canonical for Lean: an abbreviation
--   of a term ('isAbbreviation') has no type, unless it is given as a lemma
--   (one of the @roots@): it would give two ways to write the same term,
--   the abbreviation or its body.
--
--   Lean also leaves without type the symbols only met in the definitions
--   of others (@Σ.fst@ in @equivFun e = fst e@).  Here, Canonical then
--   loses the solutions that go through a term stuck on such a symbol
--   (with @Σ.fst@ without type, not even @refl : equivFun e b ≡ equivFun
--   e b@ is found): only an abbreviation of a term, which always unfolds,
--   is left without type.
relevance :: [String] -> CDecl -> TransM CDecl
relevance roots goal = case typ goal of
  Nothing -> return goal
  Just e  -> do
    defs <- seenNames <$> getSeen
    ctx' <- forM (lets e) $ \ d -> case Map.lookup (name d) defs of
      Just q | not (null (equations d)), name d `notElem` roots -> do
        abbrev <- lift (isAbbreviation q)
        return (if abbrev then d { typ = Nothing } else d)
      _ -> return d
    return goal { typ = Just e { lets = ctx' } }

-- | Is the definition an abbreviation of a term: a function of one clause
--   whose patterns are variables, with neither pattern matching nor
--   projection (@equivFun e = fst e@)?  The functions defined by pattern
--   matching are suitably complex abstractions, as the definitions by a
--   recursor in Lean.
--
--   An abbreviation of a type (@_≃_@, @isContr@) keeps its type: Canonical
--   selects the candidates for a goal by the head of their types as
--   declared, not unfolded (@e : T ≃ A@ for a @Σ@ expected).
isAbbreviation :: QName -> TCM Bool
isAbbreviation q = do
  d <- getConstInfo q
  TelV _ cod <- telView (defType d)
  return $ case theDef d of
    Function { funClauses = [cl], funProjection = Left _ }
      | isJust (clauseBody cl), not (isSort (unEl cod)) ->
          all (isVar . namedArg) (namedClausePats cl)
    _ -> False
  where
    isSort Sort{} = True
    isSort _      = False
    isVar VarP{}    = True
    isVar IApplyP{} = True
    isVar _         = False

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

-- | Declares the variables of the context, in order, and continues with the
--   type of the goal over the rest of the telescope, the bound names and the
--   signatures of the variables, in the context extended with them.
declareContext :: Telescope -> Type -> [String] -> Locals
               -> (Type -> [String] -> Locals -> TransM a) -> TransM a
declareContext tel t names locals k = case (tel, unEl t) of
  (EmptyTel, _) -> k t names locals
  (ExtendTel dom (Abs x tel'), Pi _ cod) -> do
    (d, locals') <- declare Definition (unEl (unDom dom)) x [] names locals
    pushDecl d
    addContext (x, dom) $ declareContext tel' (unAbs cod) (x : names) locals' k
  _ -> __IMPOSSIBLE__

-- | Declares an induction hypothesis, or a @let@-bound variable: the value
--   of a @let@ without metas is a rewrite rule.
declareHypothesis :: [String] -> Locals -> (String, Type, Maybe Term) -> TransM Locals
declareHypothesis names locals (n, a, mv) = do
  eqs <- case mv of
    Just v | noMetas v -> do
      ev <- toCExprAt (Just (a, a)) v names [] locals
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

-- | The boundary of the hole as constraints on its meta @mv@, in the
--   context @ctx@ of the hole: @?mv Γ[i := i0] = u₀@ for the face
--   @i = i0 ⊢ u₀@.
ownBoundary :: Telescope -> MetaId -> [([(Term, Bool)], Term)] -> TCM [(Term, Term)]
ownBoundary ctx mv bds = do
  zero <- primIZero
  one  <- primIOne
  let at face t = foldr (\ (k, b) -> applySubst (inplaceS k (if b then one else zero))) t
                        [ (k, b) | (Var k [], b) <- face ]
  return [ (at face (MetaV mv (map Apply (teleArgs ctx))), at face u) | (face, u) <- bds ]

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
        as <- allApplyElims es
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

-- | The goal of a hole with constraints, see "Constraints on the meta of
--   the hole".  @t@ is the type of the solution, a function of the refolded
--   variables; the solution is named after the meta, which the
--   constraints apply to them.  The other metas that the constraints
--   mention are found too, as in 'contGoal'.
constrainedGoal
  :: MetaId -> [(Term, Term)] -> [(MetaId, Type)] -> Type -> [String] -> Locals
  -> TransM (CDecl, Cont, Locals)
constrainedGoal mv cs ms t names locals = do
  let g = metaVarName mv
  -- The signatures of the metas unfold their types (@I → Partial φ A@ has
  -- two binders, not one), as 'declare' does.
  msigs <- forM ms $ \ (m, a) -> (,) (metaVarName m) <$> lift (tySig a)
  gsig  <- lift (tySig t)
  let locals' = foldr (\ (k, sg) -> Map.insert k (sg, Nothing)) locals ((g, gsig) : msigs)
  mdecls <- forM ms $ \ (m, a) -> fst <$> inTopContext (declare Parameter (unEl a) (metaVarName m) [] [] locals')
  (gd, _) <- declare Parameter (unEl t) g [] names locals'
  (eqs, aux) <- unzip <$> mapM (constraintEq (Just (mv, t)) names locals') cs
  -- The opaque symbols of the latest constraints are the most recent.
  pushDecls (concat (reverse aux))
  goal <- continuation (mdecls ++ [gd { equations = equations gd ++ eqs }])
  return (goal, Cont { contOuter = [], contMetas = map fst ms, contTyped = False, contSwap = 0 }, locals')

-- | A constraint as an equation.  Both sides of an equation are spines: an
--   equation between functions (@?0 x = λ h → h x@) is stated under a fresh
--   opaque symbol @W : (f : (h : _) → G') → G'@, whose arguments are
--   compared under the same binders, @W (λ h → g x h) ⤇ W (λ h → h x)@.
--   Returns the declarations of @W@ and @G'@, the most recent first.
--
--   The meta of the hole is given with the type of the solution, when the
--   constraints apply it to the refolded variables only ('cutMeta'): the
--   type of such an application is not the one that Agda would infer from
--   the type of the meta, which still binds the whole context.
constraintEq :: Maybe (MetaId, Type) -> [String] -> Locals -> (Term, Term) -> TransM (CEquation, [CDecl])
constraintEq hole names locals' (u, v) = do
  -- The type of a neutral side (@?1 = nothing@, where @nothing@ alone does
  -- not give the parameters of its type).  A side abstracted over the
  -- variables of the constraint (see 'Agda.Canonical.Hole.moveConstraint')
  -- is η-contracted first: the type of @_8 x@ is the one of @λ h → _8 x h@,
  -- and gives the types of its binders (see 'lamBinder'), in which their
  -- projections are restored.
  let inferH w = case (hole, w) of
        (Just (mv, t), MetaV m es) | m == mv, Just as <- allApplyElims es -> lift (appliedType t as)
        _ -> inferHere w names
      infer w = inferH w >>= \case
        Just a  -> return (Just a)
        Nothing -> lift (etaContract w) >>= \ w' ->
          if w' == w then return Nothing else inferH w'
  mty <- maybe (infer v) (return . Just) =<< infer u
  -- The equations of a constraint on a face need no type.
  let face w = case w of
        Lam _ b    -> face (unAbs b)
        Def q _    -> q == faceQName
        _          -> False
  when (isNothing mty && not (face u)) $
    note ("constraint " ++ P.prettyShow u ++ " = " ++ P.prettyShow v ++ ": the type of neither side is known")
  let ex = (\ a -> (a, a)) <$> mty
  eu0 <- toCExprAt ex u names [] locals'
  ev0 <- toCExprAt ex v names [] locals'
  let n = max (length (params eu0)) (length (params ev0))
  eu <- etaExtend (n - length (params eu0)) eu0
  ev <- etaExtend (n - length (params ev0)) ev0
  if n == 0 then return (CEquation (spine eu) (spine ev) True, []) else do
    w  <- freshString "W"
    gW <- freshString "G"
    let fty = CExpr (map (untyped . name) (params eu)) [] (simpleSpine gW)
        wd  = typed w (CExpr [typed "f" fty] [] (simpleSpine gW))
    return (CEquation (CSpine w [eu]) (CSpine w [ev]) True, [wd, untyped gW])

-- | The type of the application of a term of the given type, a Π-type or a
--   path type, to arguments.
appliedType :: Type -> [Arg Term] -> TCM (Maybe Type)
appliedType a [] = return (Just a)
appliedType a (x : xs) = do
  a' <- reduce a
  case unEl a' of
    Pi _ b -> appliedType (absApp b (unArg x)) xs
    _      -> pathView a' >>= \case
      PathType { pathSort = s, pathType = p } ->
        appliedType (El s (unArg p `apply` [defaultArg (unArg x)])) xs
      OType{} -> return Nothing

-- | The metas of the goal, followed by the metas that the constraints link
--   to the hole @mv@ or to them, transitively, ordered as by 'goalMetas'.
--   'Nothing' if one of them is not a local meta with a type.
linkedMetas :: MetaId -> [(MetaId, Type)] -> [(Term, Term)] -> TCM (Maybe [(MetaId, Type)])
linkedMetas mv ms cs = go (map fst ms)
  where
    go known
      | null new  = orderMetas known
      | otherwise = go (known ++ new)
      where new = nub [ x | c <- cs, let xs = allMetasList c, any (`elem` mv : known) xs
                          , x <- xs, x /= mv, x `notElem` known ]

-- | Is the type the interval @I@?
isIntervalType :: Type -> TCM Bool
isIntervalType a = reduce (unEl a) >>= \case
  Def q [] -> isInterval q
  _        -> return False

-- | The unsolved metas of a type, with their closed types, each one after
--   the metas its type contains.  'Nothing' if one of them is not a local
--   meta with a type (e.g. a sort meta).
goalMetas :: Type -> TCM (Maybe [(MetaId, Type)])
goalMetas t = orderMetas . allMetasList =<< instantiateFull t

-- | The given metas with their closed types, each one after the metas its
--   type contains (see 'goalMetas').
orderMetas :: [MetaId] -> TCM (Maybe [(MetaId, Type)])
orderMetas = go []
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
--
--   The constraints on the metas are stated on the last parameter of the
--   continuation, where all of them are bound.  They do not mention the
--   meta of the hole (see 'constrainedGoal').
contGoal
  :: [(Term, Term)]    -- ^ The constraints on the metas, in the context (with @Δ@).
  -> [(MetaId, Type)]  -- ^ The metas, with their closed types, in order.
  -> Type              -- ^ The rest of the type of the goal.
  -> Int               -- ^ The number of binders of @Δ@ coming from a path of functions.
  -> [String]          -- ^ Bound names.
  -> [CDecl]           -- ^ Binders of @Δ@ already met, the most recent first.
  -> Locals
  -> TransM (CDecl, Cont, Locals)
contGoal cs ms t swaps names delta locals = do
  t' <- instantiateFull t
  ends <- pathEnds (unEl t')
  -- A path of functions is a function to paths: its binders go to @Δ@.
  commuted <- if not (isPi (unEl t')) && isJust ends then commutePath (unEl t')
              else return Nothing
  case (commuted, unEl t') of
    (Just u, _) -> contGoal cs ms (t' { unEl = u }) (swaps + 1) names delta locals
    (_, Pi a b) | swaps > 0 || noMetas (unDom a) -> do
      x <- piBinder b
      -- The binder is declared in the context, as the variables
      -- introduced by Agda: the equations of a parameter are only
      -- constraints on its instances, so the boundary of a path would not
      -- be a rewrite rule.
      (d, locals') <- declare Definition (unEl (unDom a)) x [] names locals
      pushDecl d
      -- The constraints are moved under the binder.
      let cs' = case b of { Abs{} -> raise 1 cs; NoAbs{} -> cs }
      underBinder x a b names $ \ names' ->
        contGoal cs' ms (unAbs b) swaps names' (d : delta) locals'
    _ -> do
      -- The metas, as variables of their closed types.
      msigs <- forM ms $ \ (m, a) -> (,) (metaVarName m) <$> lift (tySig a)
      let locals' = foldr (\ (k, sg) -> Map.insert k (sg, Nothing)) locals msigs
      mdecls <- forM ms $ \ (m, a) -> fst <$> inTopContext (declare Parameter (unEl a) (metaVarName m) [] [] locals')
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
      (eqs, aux) <- unzip <$> mapM (constraintEq Nothing names locals') cs
      -- The opaque symbols of the latest constraints are the most recent.
      pushDecls (concat (reverse aux))
      let constrained = init final ++ [ d { equations = equations d ++ eqs } | d <- [last final] ]
      goal <- continuation (mdecls ++ constrained)
      let cont = Cont { contOuter = map name (reverse delta), contMetas = map fst ms
                      , contTyped = useS, contSwap = swaps }
      return (goal, cont, locals')
