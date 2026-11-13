-- | What a call to Canonical reads from the hole, besides its type and its
--   context: its cubical boundary, the constraints of Agda on its meta and
--   on the metas linked to it, its induction hypotheses and @let@-bound
--   variables, and the names in scope there, needed to print the answers
--   (see 'completeInfo').
--
--   The terms are returned in the context of the meta of the hole (see
--   'moveConstraint'), as "Agda.Canonical.ToCanonical" expects them.

module Agda.Canonical.Hole
  ( -- * The hole
    holeFunction
  , holeIsRHS
  , holeBoundary
  , retargetMeta
  , enclosingOps

    -- * Constraints
  , solvedValue
  , unblockTwins
  , metaConstraints
  , otherBoundaries

    -- * Context
  , hypotheses
  , letVariables

    -- * Printing information
  , completeInfo
  , intervalNames
  ) where

import Control.Monad (filterM, forM, join)
import Data.Functor.Identity (runIdentity)
import Data.IntMap qualified as IntMap
import Data.List (nub)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (catMaybes, listToMaybe)
import Data.Monoid (Any (..))

import Agda.Canonical.Cubical (faceTerm, halfTerm)
import Agda.Canonical.Induction (CallMatrix)
import Agda.Canonical.ToCanonical (isCubicalOp, isIntervalType)
import Agda.Canonical.Types
import Agda.Canonical.Utils (freshString, nameToString)
import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Abstract.Views (AppView' (..), appView, foldExpr, unScope)
import Agda.Syntax.Builtin (PrimitiveId (..), builtinFlat, builtinIOne, builtinIsOneEmpty, builtinItIsOne, builtinIZero, builtinSuc, builtinZero)
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty qualified as P
import Agda.Syntax.Concrete.Name qualified as C
import Agda.Syntax.Fixity (Precedence (TopCtx))
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Generic (TermLike (traverseTermM))
import Agda.Syntax.Internal.MetaVars (allMetasList, noMetas)
import Agda.Syntax.Scope.Base (isNameInScope)
import Agda.Syntax.Scope.Monad (withContextPrecedence)
import Agda.Syntax.Translation.AbstractToConcrete (abstractToConcrete_)
import Agda.TypeChecking.Free (freeIn)
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Builtin (getBuiltin', getBuiltinName', getPrimitiveName', primIOne, primIZero)
import Agda.TypeChecking.Monad.Closure (enterClosure)
import Agda.TypeChecking.Monad.Constraints (getAllConstraints)
import Agda.TypeChecking.Monad.Context (addContext, getContext, getContextArgs, getContextTelescope)
import Agda.TypeChecking.Monad.MetaVars
import Agda.TypeChecking.Monad.Open (getOpen)
import Agda.TypeChecking.Monad.Signature (HasConstInfo (getConstInfo), getDefFreeVars)
import Agda.TypeChecking.Monad.State (getScope)
import Agda.TypeChecking.Pretty (prettyTCM)
import Agda.TypeChecking.Reduce (instantiateFull)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope (flattenContext, telViewUpTo)
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.List (distinct, lastMaybe)

---------------------------------------------------------------------------
-- * The hole
---------------------------------------------------------------------------

-- | The function whose clause contains the hole, if any.
holeFunction :: InteractionId -> TCM (Maybe QName)
holeFunction ii = lookupInteractionPoint ii <&> \ ip -> case ipClause ip of
  IPClause { ipcQName = q } -> Just q
  IPNoClause                -> Nothing

-- | Is the hole the whole right-hand side of its clause?  Otherwise the
--   clause cannot be rewritten.
holeIsRHS :: InteractionId -> TCM Bool
holeIsRHS ii = do
  ip <- lookupInteractionPoint ii
  return $ case ipClause ip of
    IPClause { ipcClause = cl } | A.RHS e _ <- A.clauseRHS cl -> isHole e
    _                                                         -> False
  where
    isHole (A.ScopedExpr _ e)   = isHole e
    isHole (A.QuestionMark _ i) = i == ii
    isHole _                    = False

-- | The cubical boundary of the hole (see "Agda.Canonical.Cubical"), in its
--   context: for each face, the interval variables set to @i0@ or @i1@, and
--   the term the hole is equal to there.
holeBoundary :: InteractionId -> TCM [([(Term, Bool)], Term)]
holeBoundary ii = withInteractionId ii $ do
  ip <- lookupInteractionPoint ii
  as <- getContextArgs
  return [ ([ (Var a [], b) | (a, b) <- IntMap.toList im ], r `apply` as)
         | (im, r) <- Map.toList (getBoundary (ipBoundary ip)) ]

-- | The meta of the hole may be the η-expansion of another meta applied to
--   variables of the hole, e.g. after pruning: @?0 := λ v → _8 y v@, where
--   @_8@ cannot depend on @P@.  The solution is then the one of that meta,
--   and the constraints are on it.  Its type is closed (at the top level,
--   a meta is applied to nothing): the variables it is applied to (@y@) are
--   binders of its type, which stand for them (like refolded variables).
--   Returns that meta, and the names of these variables.
retargetMeta :: InteractionId -> TCM (Maybe (MetaId, [String]))
retargetMeta ii = withInteractionId ii $ do
  mv0   <- lookupInteractionId ii
  as    <- getContextArgs
  v     <- etaMeta <$> instantiateFull (MetaV mv0 (map Apply as))
  names <- map (fst . unDom) . telToList <$> getContextTelescope
  let n = length as
  return $ case v of
    MetaV m es | m /= mv0, Just xs <- mapM varArg es, distinct xs ->
      Just (m, [ names !! (n - 1 - i) | i <- xs ])
    _ -> Nothing

-- | The operations of Cubical Agda ('isCubicalOp') of which the hole is an
--   argument, in the right-hand side of its clause (@hcomp ? u0@): the
--   solution may use them, as if they were given as lemmas.
enclosingOps :: InteractionId -> TCM [QName]
enclosingOps ii = do
  ip <- lookupInteractionPoint ii
  case ipClause ip of
    IPClause { ipcClause = cl } | A.RHS e _ <- A.clauseRHS cl ->
      filterM isCubicalOp (nub (foldExpr heads e))
    _ -> return []
  where
    heads sub = case appView sub of
      Application h args
        | A.Def q <- unScope h, any (hasHole . namedArg) args -> [q]
      _ -> []
    hasHole = getAny . foldExpr (\case
      A.QuestionMark _ i -> Any (i == ii)
      _                  -> Any False)

---------------------------------------------------------------------------
-- * Constraints
---------------------------------------------------------------------------

-- | The meta may already be solved by unification (e.g. @?1 := 3@ once
--   @?0 + ?1 = 3@ is reduced by giving @0@): its value is a constraint too.
solvedValue :: (TCM [(Term, Term)] -> TCM [(Term, Term)]) -> MetaId -> TCM [(Term, Term)]
solvedValue inMeta mv = inMeta $ do
  as <- getContextArgs
  let u = MetaV mv (map Apply as)
  v <- instantiateFull u
  return [ (u, v) | v /= u, noMetas v ]

-- | Replaces in the constraints the metas that stand for a term whose
--   checking is postponed (e.g. @_20@ for the base @?1@ of @hcomp u ?1@,
--   until it is compatible with @u@) by this term.  Agda gives out a twin
--   of the blocked meta, which it compares with it once it is unblocked;
--   as a constraint, @_20 = ?1@ would relate two metas to find, which
--   Canonical does not find together.
unblockTwins :: [(Term, Term)] -> TCM [(Term, Term)]
unblockTwins cs = do
  vals <- fmap catMaybes $ forM (nub (concatMap allMetasList cs)) $ \ m -> do
    twin <- maybe (return Nothing) lookupLocalMeta' . (mvTwin =<<) =<< lookupLocalMeta' m
    return $ case mvInstantiation <$> twin of
      -- The value is abstracted over the context of the meta.
      Just (BlockedConst v) -> Just (m, v)
      _                     -> Nothing
  let unblock = \case
        MetaV m es | Just v <- lookup m vals -> v `applyE` es
        t                                    -> t
  if null vals then return cs else
    instantiateFull (runIdentity (traverseTermM (return . unblock) cs))

-- | Constraints of Agda on metas (e.g. @p (?0 (i = i1)) = x@ for
--   @sym p i = p ?@), moved to the context of the meta (see
--   'moveConstraint').  The constraints on other metas are kept: the
--   translation keeps those on the metas it asks Canonical to find, which
--   may depend on each other cyclically.
metaConstraints :: (TCM [(Term, Term)] -> TCM [(Term, Term)]) -> TCM [(Term, Term)]
metaConstraints inMeta = inMeta $ do
  names <- map (fst . unDom) . telToList <$> getContextTelescope
  cs    <- getAllConstraints
  fmap concat $ forM cs $ \ pc -> enterClosure (theConstraint pc) $ \case
    ValueCmp CmpEq _ u v -> do
      tel <- telToList <$> getContextTelescope
      (u', v') <- instantiateFull (u, v)
      return [ moveConstraint names tel (u', v') | not (null (allMetasList (u', v'))) ]
    -- @φ ⊢ u = v@, kept by Agda when @φ@ is blocked on a meta (e.g. the
    -- base of an @hcomp@ against its faces), see 'faceConstraints'.
    ValueCmpOnFace CmpEq phi _ u v -> do
      tel <- telToList <$> getContextTelescope
      (phi', u', v') <- instantiateFull (phi, u, v)
      if null (allMetasList (phi', u', v')) then return [] else
        map (moveConstraint names tel) <$> faceConstraints tel phi' u' v'
    _ -> return []

-- | A constraint @φ ⊢ u = v@ between partial elements @u v : (o : IsOne φ)
--   → B o@, in its context @tel@, as equations: for each assignment @ρ@ of
--   the interval variables of @φ@ to @i0@, @i1@ or none,
--
--   > Face φ[ρ, ½] uρ = Face φ[ρ, ½] vρ
--
--   where @φ[ρ, ½]@ sets the variables left by @ρ@ to @i½@.  They hold
--   exactly when the constraint does (see "Agda.Canonical.Cubical",
--   constraints on a face).
faceConstraints :: [Dom (ArgName, Type)] -> Term -> Term -> Term -> TCM [(Term, Term)]
faceConstraints tel phi u v = do
  let n = length tel
  ks <- filterM (\ k -> if k `freeIn` phi then isIntervalType (raise (k + 1) (snd (unDom (tel !! (n - 1 - k)))))
                                          else return False)
                [0 .. n - 1]
  zero <- primIZero
  one  <- primIOne
  let at s t = foldr (\ (k, w) -> applySubst (inplaceS k w)) t s
  return [ (faceTerm phiH (at s01 u), faceTerm phiH (at s01 v))
         | c <- mapM (const [Just False, Just True, Nothing]) ks
         , let s01  = [ (k, if b then one else zero) | (k, Just b) <- zip ks c ]
               phiH = at (s01 ++ [ (k, halfTerm) | (k, Nothing) <- zip ks c ]) phi ]

-- | The boundaries of the other open holes, as constraints on their metas
--   (e.g. @?82 … i0 k = ?80 … i0 k@ for the face @i = i0@ of a hole in a
--   face of @hcomp@, where @?80@ may be the meta of the hole itself), moved
--   to the context of the meta (see 'moveConstraint').
otherBoundaries :: (TCM [(Term, Term)] -> TCM [(Term, Term)]) -> InteractionId -> TCM [(Term, Term)]
otherBoundaries inMeta ii = do
  ims <- getInteractionIdsAndMetas
  fmap concat $ forM [ im | im@(ii', _) <- ims, ii' /= ii ] $ \ (ii', m) -> do
    solved <- isInstantiatedMeta m
    faces  <- Map.toList . getBoundary . ipBoundary <$> lookupInteractionPoint ii'
    if solved || null faces then return [] else do
      zero <- primIZero
      one  <- primIOne
      (tel, cs) <- withInteractionId ii' $ do
        as  <- getContextArgs
        tel <- telToList <$> getContextTelescope
        -- The interval variables of the face are set to @i0@ or @i1@.
        let at im t = foldr (\ (a, b) -> applySubst (inplaceS a (if b then one else zero))) t
                            (IntMap.toList im)
        return (tel, [ (at im (MetaV m (map Apply as)), at im (r `apply` as)) | (im, r) <- faces ])
      inMeta $ do
        names <- map (fst . unDom) . telToList <$> getContextTelescope
        instantiateFull (map (moveConstraint names tel) cs)

-- | Moves a constraint from the context @tel@ to the common prefix of this
--   context and the current one (of names @names@), then to the current
--   one.  The variables of the constraint after that prefix (e.g. @h@ in
--   @_8 x h = h x@, from comparing @λ h → h x@ with @λ v → _8 x v@) are
--   abstracted: the constraint becomes an equation between functions.
moveConstraint :: [String] -> [Dom (ArgName, Type)] -> (Term, Term) -> (Term, Term)
moveConstraint names tel (u, v) = raise (length names - j) (lams u, lams v)
  where
    j      = length (takeWhile id (zipWith (==) names (map (fst . unDom) tel)))
    lams t = foldr (\ d b -> Lam (domInfo d) (Abs (fst (unDom d)) b)) t (drop j tel)

---------------------------------------------------------------------------
-- * Context
---------------------------------------------------------------------------

-- | The induction hypotheses of the hole, as variables with the recursive
--   calls they stand for (see "Agda.Canonical.Induction"), in its context.
--   A hypothesis whose type has metas could not refer to them.
hypotheses :: TCM [(Term, Type, Int, CallMatrix)] -> String -> TCM [(String, Type, Hypothesis, CallMatrix)]
hypotheses calls self = do
  hs <- filter (\ (_, t, _, _) -> noMetas t) <$> calls
  forM hs $ \ (v, t, k, m) -> do
    n <- freshString "ih"
    -- The body of the abstracted arguments, which are placeholders.  The
    -- implicit arguments are left to Agda (@h0@ for @h0 {n}@).
    TelV tel _ <- telViewUpTo k t
    -- Printed at the top level, whatever the position of the hole (the
    -- printing adds the parentheses it needs, see 'Agda.Canonical.FromCanonical.hypPrec').
    s <- P.render <$> addContext tel (withContextPrecedence TopCtx (prettyTCM (peelLams k v)))
    -- A call of a mixfix function, such as @n + m@, needs parentheses as
    -- an argument.
    return (n, t, Hypothesis { hypCall = s, hypOperator = '_' `elem` self, hypAbstracted = k }, m)

-- | The variables bound by a @let@ around the hole (@let c x = c _ in ?@),
--   with their types and values, in its context.
letVariables :: TCM [(String, Type, Term)]
letVariables = do
  bs <- viewTC eLetBindings
  forM (Map.toAscList bs) $ \ (x, o) -> do
    LetBinding { letTerm = v, letType = a } <- getOpen o
    n <- freshString (P.prettyShow x)
    return (n, unDom a, v)

---------------------------------------------------------------------------
-- * Printing information
---------------------------------------------------------------------------

-- | Completes the information given by the translation with what comes
--   from the scope of the hole (see 'GoalInfo').
completeInfo
  :: InteractionId
  -> String                  -- ^ The function containing the hole.
  -> [String]                -- ^ The variables the meta is applied to (see 'retargetMeta').
  -> [(String, Hypothesis)]  -- ^ The induction hypotheses.
  -> GoalInfo
  -> TCM GoalInfo
completeInfo ii self pre hyps info = do
  -- Context variables the user cannot refer to (shown "not in scope").
  outOfScope <- withInteractionId ii $ do
    vars <- flattenContext <$> getContext
    fmap concat $ forM vars $ \ (CtxVar x _) -> do
      c <- abstractToConcrete_ x
      return [ P.prettyShow (nameConcrete x) | C.isInScope c == C.NotInScope ]
  -- The names under which the definitions are in scope at the hole, when
  -- they differ (@M.a@, @_×_.fst@).  The primitives on the interval are
  -- usually renamed (@_∧_@, @_∨_@, @~_@).
  prims <- catMaybes <$> mapM getPrimitiveName' [PrimIMin, PrimIMax, PrimINeg]
  let defs = Map.toList (giDefs info) ++ [ (nameToString q, q) | q <- prims ]
  aliases <- withInteractionId ii $ fmap concat $ forM defs $ \ (n, q) -> do
    c <- P.prettyShow <$> abstractToConcrete_ q
    return [ (n, c) | c /= n ]
  (projs, recCons) <- recordInfo (giDefs info)
  nat <- natConstructors (giDefs info)
  system <- systemNames ii (giDefs info)
  modPars <- withInteractionId ii $ fmap concat $ forM (Map.toList (giDefs info)) $ \ (n, q) -> do
    k <- getDefFreeVars q
    return [ (n, k) | k > 0 ]
  return info
    { giSelf = self
    , giOutOfScope = outOfScope
      -- The variables the meta is applied to come after the refolded ones,
      -- as binders of its type.
    , giRefold = giRefold info ++ pre
    , giNames = reverse pre ++ giNames info
    , giLocals = Map.adjust (drop (length pre)) "Goal" (giLocals info)
    , giHyps = Map.fromList hyps
    , giAliases = Map.fromList aliases
    , giProjs = projs, giRecCons = recCons, giNat = nat, giSystem = system
    , giModPars = Map.fromList modPars }

-- | The name under which a definition is declared to Canonical, if it is.
declaredAs :: Map String QName -> QName -> Maybe String
declaredAs defs q = listToMaybe [ n | (n, q') <- Map.toList defs, q' == q ]

-- | The names under which @i0@ and @i1@ are declared, if they are.
intervalNames :: Map String QName -> TCM (Maybe (String, String))
intervalNames defs = do
  mi0 <- getBuiltinName' builtinIZero
  mi1 <- getBuiltinName' builtinIOne
  return $ (,) <$> (declaredAs defs =<< mi0) <*> (declaredAs defs =<< mi1)

-- | The names under which @primPOr@, @isOneEmpty@, @i0@ and @i1@ are
--   declared, and @itIsOne@ as written at the hole if it is in scope, to
--   print the systems ('giSystem').
systemNames :: InteractionId -> Map String QName -> TCM (Maybe SystemNames)
systemNames ii defs = do
  por <- getPrimitiveName' PrimPOr
  emp <- getBuiltinName' builtinIsOneEmpty
  mi0 <- getBuiltinName' builtinIZero
  mi1 <- getBuiltinName' builtinIOne
  one <- getBuiltinName' builtinItIsOne
  oneName <- withInteractionId ii $ fmap join $ forM one $ \ q -> do
    inScope <- isNameInScope q <$> getScope
    if inScope then Just . P.prettyShow <$> abstractToConcrete_ q else return Nothing
  let decl = (declaredAs defs =<<)
  return $ SystemNames (decl por) (decl emp) <$> decl mi0 <*> decl mi1 <*> pure oneName

-- | The names under which the constructors of @BUILTIN NATURAL@ are
--   declared, if they are.
natConstructors :: Map String QName -> TCM (Maybe (String, String))
natConstructors defs = do
  mz <- getBuiltin' builtinZero
  ms <- getBuiltin' builtinSuc
  return $ case (mz, ms) of
    (Just (Con z _ _), Just (Con s _ _)) ->
      (,) <$> declaredAs defs (conName z) <*> declaredAs defs (conName s)
    _ -> Nothing

-- | The record projections among the declared definitions, with the number
--   of parameters of their record, and the constructors of records that have
--   no named constructor, with that number and the names of the fields.
recordInfo :: Map String QName -> TCM (Map String Int, Map String (Int, [String]))
recordInfo defs = do
  flat <- getBuiltinName' builtinFlat
  infos <- forM (Map.toList defs) $ \ (n, q) -> theDef <$> getConstInfo q >>= \case
    -- Not @♭@ (@BUILTIN FLAT@), the projection of @∞@, which is written in
    -- prefix form (Agda issue #7662).
    Function { funProjection = Right p }
      | Just q /= flat, Just r <- projProper p, projIndex p > 0 -> theDef <$> getConstInfo r >>= \case
          RecordDefn{} -> return ([(n, projIndex p - 1)], [])
          _            -> return ([], [])
    ConstructorDefn cd -> theDef <$> getConstInfo (_conData cd) >>= \case
      RecordDefn rd | not (_recNamedCon rd) ->
        return ([], [(n, (_conPars cd, map (nameToString . unDom) (_recFields rd)))])
      _ -> return ([], [])
    _ -> return ([], [])
  return (Map.fromList (concatMap fst infos), Map.fromList (concatMap snd infos))

---------------------------------------------------------------------------
-- * Utilities
---------------------------------------------------------------------------

-- | The body under the first @k@ λs of a term.
peelLams :: Int -> Term -> Term
peelLams k (Lam _ b) | k > 0 = peelLams (k - 1) (absBody b)
peelLams _ t                 = t

-- | A variable as an argument.
varArg :: Elim -> Maybe Int
varArg (Apply a) | Var i [] <- unArg a = Just i
varArg _                               = Nothing

-- | η-contracts the λs around a meta: @λ v → _8 x v@ is @_8 x@.
etaMeta :: Term -> Term
etaMeta t@(Lam _ (Abs _ b)) = case etaMeta b of
  MetaV m es | Just (Apply a) <- lastMaybe es, Var 0 [] <- unArg a
             , let es' = init es, not (0 `freeIn` es')
             -> MetaV m (strengthen __IMPOSSIBLE__ es')
  _ -> t
etaMeta t = t
