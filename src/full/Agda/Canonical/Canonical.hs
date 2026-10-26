-- | Proof search with Canonical (@C-c C-g@).
--
--   The goal is translated by "Agda.Canonical.ToCanonical", solved by
--   Canonical through "Agda.Canonical.FFI", and the solutions are printed in
--   Agda syntax by "Agda.Canonical.FromCanonical".  The options written in
--   the hole are described in "Agda.Canonical.Options".
--
--   Unless @+debug@ is given, the first solution accepted by Agda is written
--   in the file:
--
--   * if it is a recursor applied to a variable of the context, the clause
--     is split on that variable (as with @C-c C-c@) and each new clause
--     receives its right-hand side, with real recursive calls; the hidden
--     variables that the right-hand sides use are made visible
--     (@comp {p = p} refl = p@);
--
--   * otherwise the hole is filled with the term, first without implicit
--     arguments, then, if this leaves unsolved metas or constraints, with
--     all implicit arguments given in braces.
--
--   With @count := n@ (n > 1), if several solutions are accepted by Agda,
--   nothing is written: they are returned ('CanonicalChoose') for the user
--   to choose one, which 'pickCanonical' then writes.

module Agda.Canonical.Canonical
  ( callCanonical
  , pickCanonical
  ) where

import Control.Monad (filterM, forM)
import Control.Monad.Except (catchError)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Monad.State (State, evalState, get, put)
import Data.Functor ((<&>))
import Data.HashMap.Strict qualified as HMap
import Data.IntMap qualified as IntMap
import Data.List qualified as List
import Data.List (findIndex, nub)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (catMaybes, fromMaybe, isJust, isNothing, listToMaybe, mapMaybe)
import Data.Set qualified as Set

import Agda.Canonical.FFI (runCanonical)
import Agda.Canonical.FromCanonical
import Agda.Canonical.Induction (CallMatrix, compatibleSubset, inductionHypotheses, terminateTogether)
import Agda.Canonical.Interval (normaliseIntervals)
import Agda.Mimer.Monad (getEverythingInScope)
import Agda.Canonical.Recursor (withoutIHs)
import Agda.Canonical.Options
import Agda.Canonical.ToCanonical (produceCanonicalGoal, undeclaredSymbols)
import Agda.Canonical.Types
import Agda.Canonical.Utils (freshString, metaVarName, nameToString)
import Agda.Interaction.Base (Rewrite, UseForce(..))
import Agda.Interaction.BasicOps (give, parseExprIn)
import Agda.Interaction.MakeCase (makeCase, makeCaseIntro)
import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Builtin (PrimitiveId (..), builtinFlat, builtinIOne, builtinIZero, builtinSuc, builtinZero)
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty qualified as P
import Agda.Syntax.Concrete.Name qualified as C
import Agda.Syntax.Info (patNoRange)
import Agda.Syntax.Internal
import Agda.Syntax.Internal.MetaVars (allMetasList, noMetas)
import Agda.Syntax.Position (Range)
import Agda.Syntax.Abstract.Name (AbstractModule (..), isLeChildModuleOf)
import Agda.Syntax.Scope.Base (isNameInScopeUnqualified, scopePrecedence)
import Agda.Syntax.Fixity (Precedence (TopCtx))
import Agda.Syntax.Scope.Monad (freshAbstractName_, resolveModule, withContextPrecedence)
import Agda.TypeChecking.Errors (prettyError)
import Agda.TypeChecking.Free (freeIn)
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Closure (enterClosure)
import Agda.TypeChecking.Monad.Open (getOpen)
import Agda.TypeChecking.Monad.Constraints (getAllConstraints)
import Agda.Syntax.Translation.AbstractToConcrete (abstractToConcrete_)
import Agda.TypeChecking.Monad.Context (addContext, getContext, getContextArgs, getContextTelescope)
import Agda.TypeChecking.Telescope (flattenContext, telViewUpTo)
import Agda.TypeChecking.Monad.Builtin (getBuiltin', getBuiltinName', getPrimitiveName', primIOne, primIZero)
import Agda.TypeChecking.Monad.MetaVars
import Agda.TypeChecking.Monad.Signature (HasConstInfo (getConstInfo), getDefFreeVars)
import Agda.TypeChecking.Conversion (equalTerm)
import Agda.TypeChecking.Pretty (prettyTCM)
import Agda.TypeChecking.Reduce (instantiateFull)
import Agda.TypeChecking.Rules.Term (checkExpr)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad.State (getSignature)
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Lens ((^.))
import Agda.Utils.List (chopWhen, distinct, headWithDefault, lastMaybe)
import Agda.Utils.Suffix (toSubscriptDigit)

-- | Runs Canonical on a goal.
callCanonical
  :: MonadTCM tcm
  => Bool           -- ^ May the clause be split (only one goal is solved)?
  -> Rewrite        -- ^ Normalisation level (currently unused).
  -> InteractionId  -- ^ The goal.
  -> Range          -- ^ Its range.
  -> String         -- ^ Its content: the options.
  -> tcm CanonicalResult
callCanonical split _norm ii rng s =
  case parseCanonicalOptions s of
    Left err   -> return . CanonicalMessage $ "Canonical: " ++ err ++ "\n" ++ canonicalUsage
    Right opts -> do
      -- An unknown name raises the usual scope error.
      lemmas <- liftTCM $ forM (optLemmas opts) $ \ l ->
        (,) l . lemmaName <$> parseExprIn ii rng l
      case [ l | (l, Nothing) <- lemmas ] of
        []  -> liftTCM $ do
          hints <- hintNames ii (optHints opts)
          mods  <- moduleHints ii opts
          solve split ii rng opts (nub ([ q | (_, Just q) <- lemmas ] ++ hints ++ mods))
        bad -> return . CanonicalMessage $
          "Canonical: these lemmas are not names of definitions: " ++ unwords bad

---------------------------------------------------------------------------
-- * Lemmas
---------------------------------------------------------------------------

-- | The definitions added to the lemmas by @+module@ or @+scope@, as Mimer
--   does with @-m@ and @-u@: postulates, functions, datatypes, records and
--   primitives, of the module of the function containing the hole or in
--   scope unqualified (see 'usableHint').
hintNames :: InteractionId -> Hints -> TCM [QName]
hintNames _ NoHints = return []
hintNames ii mode = do
  mvar  <- lookupLocalMeta =<< lookupInteractionId ii
  self  <- holeFunction ii
  let scope = clScope (getMetaInfo mvar)
      wanted q = case mode of
        ModuleHints -> Just (qnameModule q) == (qnameModule <$> self)
        _           -> isNameInScopeUnqualified q scope
  filterM (usableHint self) (filter wanted (nub (getEverythingInScope mvar)))

-- | The definitions added to the lemmas by @+file@ and @(module := M)@:
--   those of the current file, and those of the modules @M@ (resolved in
--   the scope of the hole, so an alias such as @P@ of @import … as P@ is
--   accepted) and of their submodules, imported or not, in the order of
--   their declaration.  As for 'hintNames', only postulates, functions,
--   datatypes, records and primitives, and not the function containing the
--   hole.  Canonical receives their types and their clauses, as for the
--   lemmas.  An unknown module raises the usual scope error.
moduleHints :: InteractionId -> CanonicalOptions -> TCM [QName]
moduleHints ii opts
  | not (optFile opts), null (optModules opts) = return []
  | otherwise = do
      ms <- withInteractionId ii $ forM (optModules opts) $ \ m ->
              amodName <$> resolveModule (moduleQName m)
      local    <- HMap.keys . (^. sigDefinitions) <$> getSignature
      imported <- HMap.keys <$> useTC (stImports . sigDefinitions)
      self     <- holeFunction ii
      let inModules q = any (qnameModule q `isLeChildModuleOf`) ms
          names = [ q | optFile opts, q <- local ] ++ filter inModules (local ++ imported)
      filterM (usableHint self) (List.sort (nub names))
  where
    -- @A.B.C@ as a concrete qualified name.
    moduleQName m = case map C.simpleName (chopWhen (== '.') m) of
      [] -> __IMPOSSIBLE__
      xs -> foldr C.Qual (C.QName (last xs)) (init xs)

-- | The function whose clause contains the hole, if any.
holeFunction :: InteractionId -> TCM (Maybe QName)
holeFunction ii = lookupInteractionPoint ii <&> \ ip -> case ipClause ip of
  IPClause { ipcQName = q } -> Just q
  IPNoClause                -> Nothing

-- | Whether a definition may be added to the lemmas: a postulate, a
--   datatype, a record, a primitive, or a function other than @self@ (the
--   function containing the hole) and the functions mutual with it, and
--   other than pattern-matching λs and @with@ functions: the recursive
--   calls are the induction hypotheses.
usableHint :: Maybe QName -> QName -> TCM Bool
usableHint self q = (`catchError` \ _ -> return False) $ theDef <$> getConstInfo q <&> \case
  Axiom{}     -> True
  Datatype{}  -> True
  Record{}    -> True
  Primitive{} -> True
  Function{ funWith = NoWithFunction, funExtLam = Nothing, funMutual = m } ->
    Just q /= self && maybe True (\ s -> maybe True (s `notElem`) m) self
  _           -> False

-- | The definition named by a lemma: a function, a postulate, a datatype,
--   a constructor or a projection.
lemmaName :: A.Expr -> Maybe QName
lemmaName e = case e of
  A.ScopedExpr _ e' -> lemmaName e'
  A.Def' q _        -> Just q
  A.Con c           -> Just (A.headAmbQ c)
  A.Proj _ p        -> Just (A.headAmbQ p)
  _                 -> Nothing

---------------------------------------------------------------------------
-- * Search
---------------------------------------------------------------------------

-- | Translates the goal, calls Canonical, and displays or writes the solutions.
solve :: Bool -> InteractionId -> Range -> CanonicalOptions -> [QName] -> TCM CanonicalResult
solve split ii rng opts lemmas = do
  bds      <- holeBoundary ii
  retarget <- if null bds then retargetMeta ii else return Nothing
  mv0      <- lookupInteractionId ii
  let mv  = maybe mv0 fst retarget
      pre = maybe [] snd retarget
      -- In the context of the meta: the one of the hole, or the top level.
      inMeta :: TCM a -> TCM a
      inMeta = if isJust retarget then id else withInteractionId ii
      -- In the context of the hole: nothing for another meta.
      inHole :: TCM [a] -> TCM [a]
      inHole m = if isJust retarget then return [] else withInteractionId ii m
  cons <- concat <$> sequence
            [ solvedValue inMeta mv, metaConstraints inMeta, otherBoundaries inMeta ii ]
  -- The metas solved since the goal was created are instantiated.  The type
  -- is a Π-type over the context.
  ty   <- instantiateFull =<< getMetaTypeInContext mv
  ctx  <- inMeta $ instantiateFull =<< getContextTelescope
  self <- maybe "rec" nameToString <$> holeFunction ii
  hyps <- inHole $ hypotheses ii self
  lets <- inHole letVariables
  (goal, info0) <- produceCanonicalGoal lemmas ctx
                     ([ (n, t, Nothing) | (n, t, _, _) <- hyps ] ++ [ (n, t, Just v) | (n, t, v) <- lets ])
                     ty bds (mv, cons)
  info <- completeInfo ii self pre [ (n, h) | (n, _, h, _) <- hyps ] info0
  found <- search opts info [ (n, m) | (n, _, _, m) <- hyps ] goal
  case found of
    Left err -> return $ CanonicalMessage err
    Right (goal', info', results)
      | optDebug opts -> return . CanonicalMessage $ debugReport goal' info' hyps results
      | otherwise     -> writeSolution (optCount opts > 1) split ii rng info' results

-- | Calls Canonical, and reads the answers back.  Returns the goal as it was
--   sent, the information to print the answers, and the solutions with the
--   values of the metas.
--
--   The induction hypotheses of the context each terminate, but a solution
--   that combines several of them may not (see "Agda.Canonical.Induction").
--   The solutions whose hypotheses terminate together come first.  If
--   there is none, the search is done again with hypotheses that all
--   terminate together ('compatibleSubset'), and its solutions come first.
--   This is a prediction, finer checks being Agda's: a solution that does
--   not terminate is rejected when it is given ('tryGive').
--
--   If every solution uses the induction hypothesis of a recursor printed
--   as a pattern-matching lambda, which is not recursive, the search is
--   done again with case analyses instead of recursors ('withoutIHs'):
--   the recursion then only goes through the induction hypotheses of the
--   context, and the solutions can be written.
search :: CanonicalOptions -> GoalInfo -> [(String, CallMatrix)] -> CDecl
       -> TCM (Either String (CDecl, GoalInfo, [(CExpr, [(MetaId, CExpr)])]))
search opts info hyps goal = do
  -- The interval expressions of the answers are put in normal form
  -- (@i ∨ i@ becomes @i@).
  normalise <- maybe id normaliseIntervals <$> intervalNames (giDefs info)
  let run g = case undeclaredSymbols g of
        [] -> do
          let i = info { giContext = maybe [] lets (typ g) }
          r <- liftIO $ runCanonical g (optTimeout opts) (optCount opts)
          return $ r <&> \ as -> (g, i, mapMaybe (unwrapAnswer i . normalise) as)
        -- Canonical would reject the problem.
        xs -> return . Left $
          "Canonical: internal error, the translation of the goal does not declare "
          ++ unwords xs
      inContext f g = g { typ = (\ e -> e { lets = f (lets e) }) <$> typ g }
      terminating (d, _) = terminateTogether [ m | (n, m) <- hyps, n `Set.member` heads d ]
      terminatingFirst = fmap $ \ (g, i, rs) -> let (ok, ko) = List.partition terminating rs in (g, i, ok ++ ko)
      compatible = compatibleSubset hyps
      restricted = inContext (filter (\ d -> name d `notElem` map fst hyps || name d `elem` compatible))
  found <- run goal >>= \case
    Right (g, i, rs) | not (null rs), not (any terminating rs), length compatible < length hyps ->
      run (restricted goal) <&> \case
        Right (g', i', rs') | not (null rs') -> Right (g', i', rs' ++ rs)
        _                                    -> Right (g, i, rs)
    r -> return (terminatingFirst r)
  case found of
    Right (g, i, rs) | not (null rs), all (usesNestedIH i . fst) rs ->
      terminatingFirst <$> run (inContext (map withoutIHs) g)
    r -> return r

-- | The symbols that occur in an answer.
heads :: CExpr -> Set.Set String
heads (CExpr ps ls (CSpine h as)) =
  Set.unions (Set.singleton h : map heads as ++ [ heads t | d <- ps ++ ls, Just t <- [typ d] ])

-- | With @+debug@: the problem sent to Canonical, the induction
--   hypotheses, and the solutions.  The hints show the variables that the
--   user cannot refer to under their names, rather than @_@.
debugReport :: CDecl -> GoalInfo -> [(String, Type, Hypothesis, CallMatrix)] -> [(CExpr, [(MetaId, CExpr)])] -> String
debugReport goal info hyps results = show goal ++ "\n\n" ++ showHyps ++ showNotes ++ case results of
  []  -> "No solution found."
  [d] -> "--- Hint :\n" ++ pp d
  ds  -> "--- Hints :\n" ++ unlines [ show i ++ ". " ++ pp d | (i, d) <- zip [1 :: Int ..] ds ]
  where
    dbg = info { giOutOfScope = [] }
    pp (d, vals) = cexprToAgda False dbg d ++ concat
      [ "\n    with " ++ "_" ++ show (metaId m) ++ " := " ++ cexprToAgdaAs False dbg (metaVarName m) v
      | (m, v) <- vals ]
    showNotes
      | null (giNotes info) = ""
      | otherwise = "--- Not translated faithfully :\n" ++ unlines (giNotes info) ++ "\n"
    showHyps
      | null hyps = ""
      | otherwise = "--- Induction hypotheses :\n"
                    ++ unlines [ n ++ " = " ++ hypCall h | (n, _, h, _) <- hyps ] ++ "\n"

---------------------------------------------------------------------------
-- * The goal
---------------------------------------------------------------------------

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

-- | The meta may already be solved by unification (e.g. @?1 := 3@ once
--   @?0 + ?1 = 3@ is reduced by giving @0@): its value is a constraint too.
solvedValue :: (TCM [(Term, Term)] -> TCM [(Term, Term)]) -> MetaId -> TCM [(Term, Term)]
solvedValue inMeta mv = inMeta $ do
  as <- getContextArgs
  let u = MetaV mv (map Apply as)
  v <- instantiateFull u
  return [ (u, v) | v /= u, noMetas v ]

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
    _ -> return []

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

-- | The induction hypotheses of the hole, as variables with the recursive
--   calls they stand for (see "Agda.Canonical.Induction"), in its context.
--   A hypothesis whose type has metas could not refer to them.
hypotheses :: InteractionId -> String -> TCM [(String, Type, Hypothesis, CallMatrix)]
hypotheses ii self = do
  hs <- filter (\ (_, t, _, _) -> noMetas t) <$> inductionHypotheses ii
  forM hs $ \ (v, t, k, m) -> do
    n <- freshString "ih"
    -- The body of the abstracted arguments, which are placeholders.  The
    -- implicit arguments are left to Agda (@h0@ for @h0 {n}@).
    TelV tel _ <- telViewUpTo k t
    -- Printed at the top level, whatever the position of the hole (the
    -- printing adds the parentheses it needs, see 'hypPrec').
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
    , giProjs = projs, giRecCons = recCons, giNat = nat
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

---------------------------------------------------------------------------
-- * Writing a solution
---------------------------------------------------------------------------

-- | Writes the first solution accepted by Agda.  The metas of the goal are
--   first assigned the values found by Canonical.
--
--   If the user chooses the solution, all of them are tried (the state is
--   restored after each one), and if several are accepted, nothing is
--   written: 'CanonicalChoose' gives what each one would write.
writeSolution
  :: Bool           -- ^ Does the user choose the solution?
  -> Bool           -- ^ May the clause be split?
  -> InteractionId  -- ^ The goal.
  -> Range          -- ^ Its range.
  -> GoalInfo       -- ^ Information about the goal.
  -> [(CExpr, [(MetaId, CExpr)])]  -- ^ The solutions, with the values of the metas.
  -> TCM CanonicalResult
writeSolution _ _ _ _ _ [] = return CanonicalNoResult
writeSolution choose split ii rng info sols
  | choose = do
      tried <- forM sols $ \ sol -> do
        st <- getTC
        r  <- attempt sol
        putTC st
        return (sol, r)
      case [ (sol, res) | (sol, Right res) <- tried ] of
        []         -> rejected [ err | (_, Left err) <- tried ]
        [(sol, _)] -> firstAccepted [] [sol]
        oks        -> return $ CanonicalChoose (map snd oks) CanonicalChoices
          { ccGoal = ii, ccRange = rng, ccInfo = info, ccSolutions = map fst oks }
  | otherwise = firstAccepted [] sols
  where
    rejected errs = return . CanonicalMessage $
      "Canonical found solutions, but Agda rejected them:\n" ++ unlines errs
    firstAccepted errs [] = rejected (reverse errs)
    firstAccepted errs (sol : rest) = do
      st <- getTC
      attempt sol >>= \case
        Right res -> return res
        Left err  -> putTC st >> firstAccepted (err : errs) rest

    -- Writes a solution (in the type-checking state), or gives the reasons
    -- why Agda rejects it.
    attempt (d, vals) = do
      unassigned <- assignMetas ii rng info vals
      either (\ err -> Left (concatMap ("\n    " ++) (err : unassigned))) Right
        <$> writeOne split ii rng info d

-- | Writes the solution of the given number (counted from 1) among the
--   ones left for the user to choose.
pickCanonical :: CanonicalChoices -> Int -> TCM CanonicalResult
pickCanonical cc k = case drop (k - 1) (ccSolutions cc) of
  sol : _ | k >= 1 -> writeSolution False True (ccGoal cc) (ccRange cc) (ccInfo cc) [sol]
  _ -> return . CanonicalMessage $ "Canonical: there is no solution " ++ show k

-- | Writes a solution: as a case split if it is one, otherwise as a term.
--   The clause can only be rewritten if the hole is its whole right-hand
--   side.
writeOne :: Bool -> InteractionId -> Range -> GoalInfo -> CExpr -> TCM (Either String CanonicalResult)
writeOne split ii rng info d = do
  rewrite <- (split &&) <$> holeIsRHS ii
  msplit  <- if rewrite then caseSplit ii rng info d else return Nothing
  case msplit of
    Just res -> return (Right res)
    Nothing
      | usesNestedIH info d -> return . Left $
          cexprToAgda False info d
          ++ "\n    uses the induction hypothesis of a recursion that cannot be written as a call"
      | otherwise -> giveSolution rewrite ii rng info d

-- | The variables that the user cannot refer to, except the given ones,
--   which are made visible.
revealing :: [String] -> GoalInfo -> GoalInfo
revealing xs info = info { giOutOfScope = filter (`notElem` xs) (giOutOfScope info) }

-- | Writes a solution that is a case split ('canonicalSplit').  The
--   variables that the user cannot refer to (printed @_@) and that the
--   branches use are made visible in the new clauses, when Agda can do so.
caseSplit :: InteractionId -> Range -> GoalInfo -> CExpr -> TCM (Maybe CanonicalResult)
caseSplit ii rng info d = case canonicalSplit info d of
  Nothing -> return Nothing
  Just sp -> do
    let hidden = spHidden sp
    r <- case canonicalSplit (revealing hidden info) d of
      Just sp' | not (null hidden) -> splitClause ii rng hidden sp'
      _                            -> return Nothing
    case r of
      Just _  -> return r
      Nothing -> splitClause ii rng [] sp

-- | Writes a solution as a term.
--
--   The term is written in the clause rather than given when it is a λ,
--   whose binders become patterns (@f x = b@ rather than @f = λ x → b@), or
--   when it uses variables that the user cannot refer to (printed @_@),
--   which are made visible as @C-c C-c@ on them does.  This is done when the
--   term is accepted, or only leaves something unsolved: Agda may not infer
--   the @_@.
giveSolution :: Bool -> InteractionId -> Range -> GoalInfo -> CExpr -> TCM (Either String CanonicalResult)
giveSolution rewrite ii rng info d = do
  st0 <- getTC
  -- Parenthesised if the hole is an argument (@p (~ i)@).
  ps <- (^. scopePrecedence) <$> getInteractionScope ii
  let shown e = cexprToAgdaIn ps e info d
  r <- giveTerm ii rng (shown False) (shown True)
  let explicit = case r of
        Right (CanonicalGive s) -> s /= shown False
        _                       -> False
      hidden = outOfScopeUses explicit info d
      info'  = revealing hidden info
      lam    = lambdaClause explicit info' d
      retry  = case r of
        Right _            -> True
        Left (_, unsolved) -> unsolved
      given  = either (Left . fst) Right r
  if not rewrite || not retry || (null hidden && isNothing lam) then return given else do
    stGiven <- getTC
    putTC st0
    let (pats, rhs) = fromMaybe ([], cexprToAgda explicit info' d) lam
    rewriteClause ii rng hidden pats rhs >>= \case
      Just res -> return (Right res)
      Nothing  -> putTC stGiven >> return given

-- ** Metas

-- | Assigns to the metas of the goal the values found by Canonical, in
--   order (the type of a meta may contain the previous ones).  A value is a
--   closed function of the context of its meta: it is checked against the
--   closed type of the meta, then unified with the meta applied to its
--   context.  It is printed first without, then with implicit arguments.
--
--   A value that Agda rejects (e.g. a name out of scope) is skipped: Agda
--   may still find the meta when the solution is given.  Returns the reasons.
assignMetas :: InteractionId -> Range -> GoalInfo -> [(MetaId, CExpr)] -> TCM [String]
assignMetas ii rng info vals = withInteractionId ii $ concat <$> mapM one vals
  where
    one (m, v) = do
      let shown e = cexprToAgdaAs e info (metaVarName m) v
      st <- getTC
      r1 <- assign m (shown False)
      r  <- case r1 of
        Right () -> return r1
        Left _   -> putTC st >> assign m (shown True)
      case r of
        Right () -> return []
        Left err -> do
          putTC st
          return ["cannot assign _" ++ show (metaId m) ++ " := " ++ shown False ++ ": " ++ err]

    assign m s = (`catchError` \ err -> Left . P.render <$> prettyError err) $ do
      mv <- lookupLocalMeta m
      case mvJudgement mv of
        HasType{ jMetaType = a } -> do
          e  <- parseExprIn ii rng s
          u  <- checkExpr e =<< instantiateFull a
          es <- getMetaContextArgs mv
          t  <- getMetaTypeInContext m
          equalTerm t (MetaV m (map Apply es)) (u `apply` es)
          return (Right ())
        IsSort{} -> return (Left "sort metas are not supported")

-- ** Terms

-- | Fills the hole with the first expression, or with the second one (the
--   same with implicit arguments) if the first one leaves unsolved metas or
--   constraints.  If both are rejected or leave something unsolved, the
--   state is restored and the reason is returned, with whether the last
--   expression was only left unsolved (rather than rejected).
giveTerm :: InteractionId -> Range -> String -> String -> TCM (Either (String, Bool) CanonicalResult)
giveTerm ii rng s1 s2 = do
  st <- getTC
  r1 <- tryGive ii rng s1
  case r1 of
    Right True -> done s1
    _ | s1 == s2 -> putTC st >> failed r1
    _ -> do
      putTC st
      r2 <- tryGive ii rng s2
      case r2 of
        Right True -> done s2
        _          -> putTC st >> failed r2
  where
    done s = return (Right (CanonicalGive s))
    failed r = return . Left $ case r of
      Left err -> (s1 ++ "\n    " ++ err, False)
      Right _  -> (s1 ++ "\n    leaves unsolved metas or constraints", True)

-- | Gives an expression.  Returns whether no new meta or constraint is left
--   unsolved, or the error message.
--
--   The expression is rejected if the function containing the hole no
--   longer passes the termination check: 'give' checks it again, but only
--   warns.
tryGive :: InteractionId -> Range -> String -> TCM (Either String Bool)
tryGive ii rng s = do
  ms0 <- getOpenMetas
  cs0 <- length <$> getAllConstraints
  w0  <- terminationIssues
  r <- (Right <$> (give WithoutForce ii =<< parseExprIn ii rng s))
         `catchError` \ err -> Left . P.render <$> prettyError err
  case r of
    Left err -> return (Left err)
    Right _  -> do
      ms1 <- getOpenMetas
      cs1 <- length <$> getAllConstraints
      new <- filter (`notElem` w0) <$> terminationIssues
      if not (null new) then Left . unlines <$> mapM (fmap P.render . prettyTCM) new else
        return (Right (all (`elem` ms0) ms1 && cs1 <= cs0))
  where
    terminationIssues = useTC stTCWarnings <&> \ ws ->
      [ w | w <- Set.toList ws, TerminationIssue{} <- [tcWarning w] ]

-- ** Clauses

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

-- | Rewrites the clause of the hole: makes the given hidden variables
--   visible, as @C-c C-c@ on them (or only expands an ellipsis, as
--   @C-c C-c@ on @.@), adds the given patterns, and gives the right-hand
--   side.  The new clause is not checked: Agda checks it when the file is
--   reloaded.  'Nothing' if Agda cannot make the variables visible (e.g.
--   module parameters, hidden λ-bound variables), or in an extended λ.
rewriteClause :: InteractionId -> Range -> [String] -> [(Maybe String, Hiding)] -> String
              -> TCM (Maybe CanonicalResult)
rewriteClause ii rng xs pats rhs = (`catchError` \ _ -> return Nothing) $ do
  (f, casectxt, cs) <- makeCase ii rng (if null xs then "." else unwords xs)
  case cs of
    [cl] | isNothing casectxt ->
      fmap (\ cl' -> CanonicalMakeCase f [(cl', Just rhs)]) <$> addPatterns pats cl
    _ -> return Nothing

-- | Adds patterns at the end of the left-hand side of a clause: a variable
--   with the given name, or @_@.
addPatterns :: [(Maybe String, Hiding)] -> A.Clause -> TCM (Maybe A.Clause)
addPatterns xs cl = case A.lhsCore lhs of
  core@A.LHSHead{ A.lhsPats = ps } -> do
    new <- forM xs $ \ (mx, h) -> setHiding h . defaultNamedArg <$> case mx of
      Nothing -> return (A.WildP patNoRange)
      Just x  -> A.VarP . A.mkBindName <$> freshAbstractName_ (C.simpleName x)
    return (Just cl { A.clauseLHS = lhs { A.lhsCore = core { A.lhsPats = ps ++ new } } })
  _ -> return Nothing
  where
    lhs = A.clauseLHS cl

-- ** Case splits

-- | Splits the clause of the hole, and fills the new clauses.  The given
--   hidden variables are made visible, as @C-c C-c@ on their names.
--   'Nothing' if Agda cannot split there, or if the clauses produced by the
--   split do not have the expected shape.
splitClause :: InteractionId -> Range -> [String] -> Split -> TCM (Maybe CanonicalResult)
splitClause ii rng hidden sp = (`catchError` \ _ -> return Nothing) $ do
  ip <- lookupInteractionPoint ii
  let origPats = case ipClause ip of
        IPClause { ipcClause = cl } -> Just (A.spLhsPats (A.clauseLHS cl))
        IPNoClause                  -> Nothing
  case (origPats, spTarget sp) of
    -- Split on a pattern variable of the clause.  The revealed variables
    -- are new patterns, which shift the position of the split one.
    (Just ops, SplitVar x) | Just i <- findIndex (isVarP x . namedArg) ops -> do
      (f, casectxt, cs) <- makeCase ii rng (unwords (x : hidden))
      let original ps = [ j | (j, q) <- zip [0 ..] ps, not (revealed q) ]
      finish f casectxt (\ ps -> listToMaybe (drop i (original ps))) (const []) cs
    -- Introduce the arguments of the goal, and split on the k-th one.  The
    -- introduced explicit arguments follow the explicit patterns of the
    -- clause; the implicit ones are not written.
    (Just ops, SplitArg k hs) | k < length hs, visible (hs !! k) -> do
      (f, casectxt, cs) <- makeCaseIntro ii rng k hidden
      let e0       = length (filter visible ops)
          visPos t = e0 + length (filter visible (take t hs))
          nthVisible ps n = listToMaybe (drop n [ j | (j, q) <- zip [0 ..] ps, visible q ])
          params ps = [ if visible h then nthVisible ps (visPos t) >>= varName . namedArg . (ps !!)
                        else Nothing
                      | (t, h) <- zip [0 ..] hs ]
      finish f casectxt (\ ps -> nthVisible ps (visPos k)) params cs
    _ -> return Nothing
  where
    isVarP x p = case p of
      A.VarP b -> P.prettyShow (A.unBind b) == x
      _        -> False
    -- A hidden pattern added to make a variable visible, @{x = x}@.
    revealed q = not (visible q)
      && any (`elem` hidden) (catMaybes [bareNameOf q, varName (namedArg q)])
    finish f casectxt pos params cs
      | isJust casectxt = return Nothing
      | otherwise       = do
          mcs <- mapM (fillClause sp hidden pos params) cs
          return $ CanonicalMakeCase f <$> sequence mcs

-- | Fills a clause produced by a split: binds the fields that the
--   right-hand side needs, and computes the right-hand side.
--   Absurd clauses are kept as they are.  'Nothing' if a revealed variable
--   is not bound by the clause (e.g. the split has refined it).
fillClause
  :: Split
  -> [String]                                       -- ^ Variables made visible.
  -> ([NamedArg A.Pattern] -> Maybe Int)            -- ^ Position of the split pattern.
  -> ([NamedArg A.Pattern] -> [Maybe String])       -- ^ Names of the introduced arguments.
  -> A.Clause
  -> TCM (Maybe (A.Clause, Maybe String))
fillClause sp hidden pos params cl = case A.lhsCore lhs of
  core@A.LHSHead{ A.lhsPats = ps0 }
    | let ps = uniquePatVars ps0, Just i <- pos ps, i < length ps -> case namedArg (ps !! i) of
    A.AbsurdP{} -> return (Just (cl, Nothing))
    A.ConP ci c sub
      | (br : _) <- [ b | b <- spBranches sp, sbCtorName b == Just (A.headAmbQ c) ]
      , let taken = concatMap (patVars . namedArg) ps
      , all (`elem` taken) hidden -> do
          mfs <- alignFields taken (sbFields br) sub
          case mfs of
            Nothing -> return Nothing
            Just (sub', names, new) -> do
              let ps'  = take i ps ++ [setNamedArg (ps !! i) (A.ConP ci c sub')] ++ drop (i + 1) ps
                  cn   = ClauseNames
                    { cnFields = names
                    , cnArgs   = sequence [ if j == i then Just Nothing else Just <$> varName (namedArg q)
                                          | (j, q) <- zip [0 ..] ps, visible q ]
                    , cnUsed   = taken ++ new
                    , cnParams = params ps
                    -- A revealed pattern may be positional (@{a}@): the
                    -- argument is then named after the variable.
                    , cnHidden = [ (a, v) | q <- ps, not (visible q), Just v <- [varName (namedArg q)]
                                          , let a = fromMaybe v (bareNameOf q), a `elem` hidden ]
                    }
                  cl'  = cl { A.clauseLHS = lhs { A.lhsCore = core { A.lhsPats = ps' } } }
              return (Just (cl', Just (sbRHS br cn)))
    _ -> return Nothing
  _ -> return Nothing
  where
    lhs = A.clauseLHS cl

-- | Gives distinct names to the pattern variables, so that the names used
--   in the right-hand side are the ones printed.  Only the concrete names
--   change, so references (e.g. in dot patterns) follow.
uniquePatVars :: [NamedArg A.Pattern] -> [NamedArg A.Pattern]
uniquePatVars ps = evalState (mapM (traverse (traverse pat)) ps) Set.empty
  where
    pat :: A.Pattern -> State (Set.Set String) A.Pattern
    pat p = case p of
      A.VarP b        -> A.VarP <$> rename b
      A.ConP i c sub  -> A.ConP i c <$> mapM (traverse (traverse pat)) sub
      A.AsP i b q     -> A.AsP i <$> rename b <*> pat q
      _               -> return p
    rename (A.BindName x) = do
      used <- get
      let base = P.prettyShow (A.nameConcrete x)
          new  = headWithDefault base
                   [ n | n <- base : [ base ++ map toSubscriptDigit (show k) | k <- [1 :: Int ..] ]
                       , n `Set.notMember` used ]
      put (Set.insert new used)
      return (A.BindName x { A.nameConcrete = C.simpleName new })

-- | The name of a variable pattern.
varName :: A.Pattern -> Maybe String
varName p = case p of
  A.VarP b -> Just (P.prettyShow (A.unBind b))
  _        -> Nothing

-- | The variables bound by a pattern.
patVars :: A.Pattern -> [String]
patVars p = case p of
  A.VarP b        -> [P.prettyShow (A.unBind b)]
  A.ConP _ _ sub  -> concatMap (patVars . namedArg) sub
  A.AsP _ b q     -> P.prettyShow (A.unBind b) : patVars q
  _               -> []

-- | Matches the fields of a constructor with the patterns written by Agda.
--
--   A used field whose pattern is @_@ or missing (Agda omits implicit
--   fields) gets a fresh variable; @{_}@ is inserted before an implicit
--   field that is added, to keep the positions.  Returns the new patterns,
--   the name of each field if bound, and the new names; 'Nothing' if a used
--   field is matched by another kind of pattern.
alignFields
  :: [String]                  -- ^ Names already bound by the clause.
  -> [(String, Hiding, Bool)]  -- ^ Fields: suggested name, visibility, used.
  -> [NamedArg A.Pattern]      -- ^ Patterns of the fields, as written by Agda.
  -> TCM (Maybe ([NamedArg A.Pattern], [Maybe String], [String]))
alignFields taken0 fields0 pats0 = go (Set.fromList taken0) fields0 pats0
  where
    go _ [] [] = return (Just ([], [], []))
    go _ [] _  = return Nothing
    go taken fs@((x, h, used) : rest) qs = case qs of
      q : qs' | visible q == visible h, isNothing (bareNameOf q) -> case namedArg q of
        A.VarP b -> cons q (Just (bindName b)) [] <$> go taken rest qs'
        A.WildP{} | used -> do
          (n, taken') <- freshVar taken x
          cons (setNamedArg q (A.VarP n)) (Just (bindName n)) [bindName n] <$> go taken' rest qs'
        _ | used      -> return Nothing
          | otherwise -> cons q Nothing [] <$> go taken rest qs'
      _ | visible h -> return Nothing
        | used -> do
            (n, taken') <- freshVar taken x
            cons (hidden h (A.VarP n)) (Just (bindName n)) [bindName n] <$> go taken' rest qs
        | laterUsed fs -> cons (hidden h (A.WildP patNoRange)) Nothing [] <$> go taken rest qs
        | otherwise    -> fmap (\ (ps, ns, new) -> (ps, Nothing : ns, new)) <$> go taken rest qs

    cons p n new = fmap (\ (ps, ns, new') -> (p : ps, n : ns, new ++ new'))
    hidden h p   = setHiding h (defaultNamedArg p)
    bindName     = P.prettyShow . A.unBind
    -- Is an implicit field after this one, in the same run of implicit
    -- fields, used?
    laterUsed (_ : rest) = any (\ (_, _, u) -> u) (takeWhile (\ (_, h, _) -> not (visible h)) rest)
    laterUsed []         = False

    freshVar taken x = do
      let n = headWithDefault "x" [ y | y <- iterate (++ "'") x, y `Set.notMember` taken ]
      a <- freshAbstractName_ (C.simpleName n)
      return (A.mkBindName a, Set.insert n taken)
