{-# OPTIONS_GHC -Wunused-imports #-}
{-# LANGUAGE NondecreasingIndentation #-}

-- | Library search: the @exact?@ and @apply?@ commands, modelled after
--   Lean's @Lean.Meta.LibrarySearch@.
--
--   The search proceeds in three steps.
--
--   1. /Candidates./ We collect every definition of the loaded signature that
--      could be referred to from the hole: the names in scope at the hole, and
--      the publicly exported definitions of every (transitively) imported
--      module, even if they are not in scope.  Generated definitions (with
--      functions, extended lambdas), module copies that are not in scope and
--      the function being defined are skipped.
--
--   2. /Filtering./ The conclusion of each candidate (its type with all the
--      Π-binders stripped, after weak head normalisation) is summarised by a
--      'KTree': its head symbol and, up to a fixed depth, the head symbols of
--      its visible arguments.  The candidate's own variables become wildcards.
--      A candidate is kept if its 'KTree' matches the one of the goal; the
--      candidates are tried in order of decreasing specificity.  As in Lean,
--      candidates whose conclusion is a wildcard (@⊥-elim@, @id@, ...) or an
--      equation between two wildcards (@sym@, @trans@, ...) are dropped: they
--      would match every goal.
--
--   3. /Unification./ A candidate is applied to fresh metavariables, its type
--      is unified with the goal type (rejecting candidates that leave
--      constraints), and the visible arguments that are not determined by
--      unification become subgoals.  Each subgoal is then attacked by a small
--      bounded-depth search in the spirit of Lean's @solve_by_elim@, using the
--      local variables and the constructors of the subgoal's type.
--
--   @exact?@ returns the first candidate for which all the subgoals are
--   solved.  @apply?@ returns the candidates that unify with the goal,
--   where the unsolved subgoals are left as new holes.
--
--   Every attempt is run in a saved state, so the search never changes the
--   type checking state.

module Agda.Interaction.LibrarySearch
  ( LibrarySearchMode(..)
  , LibrarySearchResult(..)
  , LibrarySuggestion(..)
  , librarySearch
  ) where

import Prelude hiding (null)

import Control.Monad
import Control.Monad.Except (catchError, throwError)
import Control.Monad.IO.Class (liftIO)
import Agda.Utils.Impossible (catchImpossible)

import Data.HashMap.Strict qualified as HMap
import Data.IORef
import Data.List (sortBy)
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Maybe (catMaybes)
import Data.Ord (comparing, Down(..))
import Data.Set (Set)
import Data.Set qualified as Set

import Agda.Interaction.Base (Rewrite)
import Agda.Interaction.BasicOps (normalForm)

import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty qualified as P
import Agda.Syntax.Concrete.Name qualified as C
import Agda.Syntax.Internal
import Agda.Syntax.Literal (Literal)
import Agda.Syntax.Position (Range)
import Agda.Syntax.Scope.Base
import Agda.Syntax.Internal.MetaVars (allMetas)
import Agda.Syntax.Translation.AbstractToConcrete (abstractToConcrete_)
import Agda.Syntax.Translation.InternalToAbstract (reify, blankNotInScope)

import Agda.TypeChecking.Constraints (noConstraints)
import Agda.TypeChecking.Conversion (equalTerm, leqType)
import Agda.TypeChecking.MetaVars (newValueMeta, newInstanceMeta)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Primitive (getBuiltinName)
import Agda.TypeChecking.Reduce (reduce, instantiateFull, simplify)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope (telView, flattenTel)

import Agda.Utils.List1 qualified as List1
import Agda.Utils.Monad (ifM, unlessM)
import Agda.Utils.Tuple (first)
import Agda.Utils.Null
import Agda.Utils.Size
import Agda.Utils.Time (getCPUTime, fromMilliseconds)

------------------------------------------------------------------------
-- * Interface
------------------------------------------------------------------------

data LibrarySearchMode
  = SearchExact  -- ^ @exact?@: close the goal.
  | SearchApply  -- ^ @apply?@: refine the goal, leaving subgoals.
  deriving (Eq, Show)

-- | A solution, or partial solution, found by the search.
data LibrarySuggestion = LibrarySuggestion
  { sugExpr     :: String
    -- ^ The expression to insert in the hole, with a @?@ for each subgoal.
  , sugSubgoals :: [String]
    -- ^ The types of the remaining subgoals, in the order of the @?@s.
  , sugInScope  :: Bool
    -- ^ Is the lemma in scope at the hole?  If not, its module has to be
    --   imported or opened before the suggestion can be used.
  }

data LibrarySearchResult
  = LibrarySearchFailed String
    -- ^ Nothing was found; the string explains why.
  | LibrarySearchExact LibrarySuggestion
    -- ^ Result of @exact?@: a complete solution.
  | LibrarySearchApply [LibrarySuggestion]
    -- ^ Result of @apply?@: the suggestions, best first.

------------------------------------------------------------------------
-- * Parameters
------------------------------------------------------------------------

-- | Depth of the 'KTree' summarising a conclusion.
keyDepth :: Int
keyDepth = 3

-- | Depth of the @solve_by_elim@ search for the subgoals.
elimDepth :: Int
elimDepth = 3

-- | Number of refinement steps the @solve_by_elim@ search may take for a
--   single candidate.
elimFuel :: Int
elimFuel = 200

-- | CPU time budget of the whole search, in milliseconds.
searchTimeout :: Integer
searchTimeout = 5000

-- | Maximal number of suggestions returned by @apply?@.
maxSuggestions :: Int
maxSuggestions = 20

------------------------------------------------------------------------
-- * Keys
------------------------------------------------------------------------

data Key
  = KDef QName
  | KCon QName
  | KLit Literal
  | KSort
  | KPi
  | KLocal       -- ^ A variable of the context of the hole.
  deriving Eq

-- | A summary of the shape of a term, used to filter the candidates before
--   trying to unify them with the goal.
data KTree
  = KNode Key [KTree]
  | KAny         -- ^ Wildcard: matches every term.

-- | @termKey bound depth v@ summarises @v@.  The variables with index below
--   @bound@ are pattern variables (bound by the Π-binders that were stripped)
--   and become wildcards.  Only the visible arguments are taken into
--   account: hidden arguments are mostly determined by the visible ones, and
--   levels and types are often written differently.
termKey :: Int -> Int -> Term -> KTree
termKey bound = go
  where
    go d v | d <= 0 = KAny
    go d v = case v of
      Def f es   -> KNode (KDef f) (args d es)
      Con c _ es -> KNode (KCon (conName c)) (args d es)
      Lit l      -> KNode (KLit l) []
      Sort{}     -> KNode KSort []
      Pi{}       -> KNode KPi []
      -- A projection of a variable, @x .f a b@ (the operations of an
      -- algebraic structure): summarised by the last projection and the
      -- arguments after it, which is what the term is about.
      Var _ es
        | (p, rest) : _ <- lastProj es -> KNode (KDef p) (args d rest)
      Var i _
        | i < bound -> KAny
        | otherwise -> KNode KLocal []
      Lam{}      -> KAny
      Level{}    -> KAny
      MetaV{}    -> KAny
      DontCare{} -> KAny
      Dummy{}    -> KAny
    args d es = [ go (d - 1) (unArg a) | Apply a <- es, visible a ]
    -- The last projection in the eliminations, with the ones after it.
    lastProj es = reverse [ (p, rest) | (Proj _ p : rest) <- List.tails es ]

-- | Do two summaries match?  If they do, return the number of concrete
--   nodes that matched, which measures how specific the match is.
matchKey :: KTree -> KTree -> Maybe Int
matchKey KAny _ = Just 0
matchKey _ KAny = Just 0
matchKey (KNode k ts) (KNode k' ts')
  | k == k'   = (1 +) . sum <$> zipWithM matchKey ts ts'
  | otherwise = Nothing

-- | Summaries that match (nearly) every goal.  Candidates with such a
--   conclusion are dropped, as in Lean.
isTrivialKey :: Maybe QName -> KTree -> Bool
isTrivialKey _ KAny = True
isTrivialKey (Just eq) (KNode (KDef f) ts) | f == eq = all isAny ts
  where
    isAny KAny = True
    isAny _    = False
isTrivialKey _ _ = False

------------------------------------------------------------------------
-- * Heads
------------------------------------------------------------------------

-- | Something the goal can be refined with: a lemma, a local variable or a
--   constructor.
data Head = Head
  { headName    :: Maybe QName
  , headTerm    :: Term
  , headType    :: Type
  , headSkip    :: Int
    -- ^ Number of leading arguments that are not applied to the term
    --   (the parameters of a constructor).
  , headArity   :: Int
    -- ^ Number of Π-binders of the type, after reduction.
  , headKey     :: KTree
    -- ^ Summary of the conclusion of the type.
  , headInScope :: Bool
  }

-- | Build a head from a term and its type (in the current context).
mkHead :: Maybe QName -> Bool -> Int -> Term -> Type -> TCM Head
mkHead x inScope skip v t = do
  TelV tel core <- telView t
  let n = size tel
  return Head
    { headName    = x
    , headTerm    = v
    , headType    = t
    , headSkip    = skip
    , headArity   = n
    , headKey     = termKey n keyDepth (unEl core)
    , headInScope = inScope
    }

-- | The head for a global definition, if it can be used as a term.
globalHead :: Bool -> QName -> TCM (Maybe Head)
globalHead inScope q = (`catchError` \ _ -> return Nothing) $
  getConstInfo' q >>= \case
    Left _    -> return Nothing
    Right def -> do
      erasedCxt <- hasQuantity0 <$> viewTC eQuantity
      if hasQuantity0 def && not erasedCxt || isIrrelevant def then return Nothing else do
      pars <- freeVarsToApply q
      let asDef = Just (Def q [] `apply` pars, 0)
          term = case theDef def of
            c@Constructor{} -> Just (Con (conSrcCon c) ConOCon [], conPars c - length pars)
            d@Function{}
              | isExtendedLambda d || isWithFunction d || isMacro d
                                       -> Nothing
            -- Projections and projection-like functions are applied
            -- without their parameters in the internal syntax; their
            -- type still has them.  'projDropPars' gives a term that
            -- discards them (as in Agda.TypeChecking.Rules.Application).
            Function{ funProjection = Right proj }
                                       -> Just (projDropPars proj ProjSystem `apply` pars, 0)
            Function{}                 -> asDef
            Axiom{}                    -> asDef
            Datatype{}                 -> asDef
            Record{}                   -> asDef
            Primitive{}                -> asDef
            AbstractDefn{}             -> asDef
            PrimitiveSort{}            -> Nothing
            GeneralizableVar{}         -> Nothing
            DataOrRecSig{}             -> Nothing
      forM term $ \ (v, skip) ->
        mkHead (Just q) inScope skip v (defType def `piApply` pars)

-- | The local variables in scope, as heads.
localHeads :: TCM [Head]
localHeads = do
  vars  <- getContextVars
  terms <- getContextTerms
  tys   <- flattenTel <$> getContextTelescope
  fmap catMaybes $ forM (zip3 vars terms tys) $ \ ((_, x), v, t) -> do
    c <- abstractToConcrete_ (unDom x)
    if C.isInScope c /= C.InScope then return Nothing else
      Just <$> mkHead Nothing True 0 v (unDom t)

-- | The constructors of the (reduced) target of the given type, as heads.
constructorHeads :: Type -> TCM [Head]
constructorHeads t = do
  TelV _ core <- telView t
  case unEl core of
    Def d _ -> getConstInfo' d >>= \case
      Right def -> case theDef def of
        Datatype{ dataCons = cs } -> catMaybes <$> mapM (globalHead True) cs
        r@Record{}                -> maybe [] pure <$> globalHead True (recCon r)
        _                         -> return []
      Left _ -> return []
    _ -> return []

-- | All the global candidates for library search.
libraryCandidates :: ScopeInfo -> Maybe QName -> TCM [Head]
libraryCandidates scope self = do
  st <- getTC
  let local    = HMap.keys $ st ^. stSignature . sigDefinitions
      imported = HMap.keys $ st ^. stImports   . sigDefinitions
      importedMods = Set.map moduleNameId $ st ^. stImportedModulesTransitive
      fromImportedModule q = let NameId _ h = nameId (qnameName q) in h `Set.member` importedMods
      inScope q = isNameInScope q scope
      -- A definition of the current file can only be used if it is in scope
      -- (otherwise it is defined later, or in a private block).
      okLocal q = inScope q && Just q /= self
  -- The scopes of the modules that are imported only transitively are not
  -- part of the current scope: we take them from their interfaces.
  visited <- getVisitedModules
  let exported = exportedNames $
        scope ^. scopeModules :
        [ iScope (miInterface mi) | mi <- Map.elems visited ]
      okImported q
        | inScope q = True
        | otherwise = fromImportedModule q && q `Set.member` exported
  defs <- forM (filter okLocal local ++ filter okImported imported) $ \ q -> do
    -- Module copies (from module applications) are only interesting if
    -- they are in scope; otherwise we would find each lemma many times.
    copy <- either (const True) defCopy <$> getConstInfo' q
    if copy && not (inScope q) then return Nothing else
      withSavedState $ guardImpossible "head" (Just q) $ globalHead (inScope q) q
  return $ catMaybes defs

-- | The names that the given modules export, whether or not they are in
--   scope themselves.
exportedNames :: [Map.Map ModuleName Scope] -> Set QName
exportedNames scopes = Set.fromList
  [ anameName a
  | ss <- scopes
  , s  <- Map.elems ss
  , (PublicNS, ns) <- scopeNameSpaces s
  , as <- Map.elems $ nsNames ns
  , a  <- List1.toList as
  ]

------------------------------------------------------------------------
-- * Refinement
------------------------------------------------------------------------

-- | Skip a candidate whose processing raises @__IMPOSSIBLE__@ (an internal
--   error of Agda on an unexpected term), rather than failing the whole
--   search.  The state is restored by the caller ('withSavedState').
guardImpossible :: String -> Maybe QName -> TCM (Maybe a) -> TCM (Maybe a)
guardImpossible phase q m = m `catchImpossible` \ err -> do
  reportSLn "interaction.search" 10 $ "Library search: internal error in " ++ phase
    ++ " for " ++ maybe "?" P.prettyShow q ++ ", candidate skipped: " ++ show err
  return Nothing

-- | Run the computation, then restore the state.
withSavedState :: TCM a -> TCM a
withSavedState m = do
  st <- getTC
  (m <* putTC st) `catchError` \ err -> putTC st >> throwError err

-- | Run the computation; if it fails (returns 'False' or throws an
--   error), restore the state.
attempt :: TCM Bool -> TCM Bool
attempt m = do
  st <- getTC
  ok <- m `catchError` \ _ -> return False
  unless ok $ putTC st
  return ok

-- | The term denoting a metavariable in the current context.
metaTerm :: MetaId -> TCM Term
metaTerm m = do
  mv <- lookupLocalMeta m
  MetaV m . map Apply <$> getMetaContextArgs mv

-- | Apply a term to fresh metavariables for the first @k@ arguments.
--   The first @skip@ arguments are only used in the type, not applied to
--   the term (constructor parameters).  Returns the metas, each with
--   whether it stands for a visible argument.
applyToMetas :: Int -> Int -> Term -> Type -> TCM (Term, Type, [(MetaId, Bool)])
applyToMetas k skip v t
  | k <= 0    = return (v, t, [])
  | otherwise = do
      t <- reduce t
      case unEl t of
        Pi dom b -> do
          (m, u) <- if isInstance dom
                    then newInstanceMeta "" (unDom dom)
                    else newValueMeta DontRunMetaOccursCheck CmpLeq (unDom dom)
          let v' | skip > 0  = v
                 | otherwise = v `apply` [setOrigin Inserted $ u <$ argFromDom dom]
          (v'', t', ms) <- applyToMetas (k - 1) (skip - 1) v' (absApp b u)
          return (v'', t', (m, skip <= 0 && visible dom) : ms)
        _ -> return (v, t, [])

-- | Refine the metavariable with the head.  Returns the subgoals: the metas
--   of the visible arguments that unification did not determine.
refineWith :: Head -> MetaId -> TCM (Maybe [MetaId])
refineWith h m = (`catchError` \ _ -> return Nothing) $ do
  goal <- reduce =<< instantiateFull =<< getMetaTypeInContext m
  TelV gtel _ <- telView goal
  let k = headArity h - size gtel
  if k < 0 then return Nothing else do
  (v, t, ms) <- applyToMetas k (headSkip h) (headTerm h) (headType h)
  -- Agda's unifier postpones problems like @?m + ?n = a + b@, since @_+_@
  -- is not injective.  As Lean does, we first match the conclusion of the
  -- head against the goal syntactically, to instantiate the metas that
  -- occur in rigid positions.  The type comparison below checks the result.
  when (null gtel) $ do
    t' <- reduce t
    n  <- size <$> getContext
    forM_ (firstOrderMatch n (Set.fromList (map fst ms)) (unEl t') (unEl goal)) $ \ (x, u) ->
      unlessM (isInstantiatedMeta x) $ void $ attempt $ do
        xt <- getMetaTypeInContext x
        xv <- metaTerm x
        noConstraints $ equalTerm xt xv u
        return True
  mv <- metaTerm m
  noConstraints $ do
    leqType t goal
    equalTerm goal mv v
  -- Instance arguments may have become solvable.
  solveAwakeConstraints
  -- A visible argument may be instantiated by a term that still contains
  -- metas (e.g. by pruning): those metas are the subgoals.
  Just . List.nub . concat <$> mapM (openMetasOf <=< metaTerm) [ x | (x, True) <- ms ]

-- | The open metas of a term, after instantiation.
openMetasOf :: Term -> TCM [MetaId]
openMetasOf v = List.nub . allMetas (: []) <$> instantiateFull v

-- | Syntactic first-order matching of a term containing the given metas
--   against a term without them.  Returns candidate instantiations; they
--   are not checked.  Does not go under binders.
--
--   The metas live in the current context, of length @n@: they are
--   applied to the @n@ context variables, and possibly to further
--   eliminations, as in @?r .f ?a@ (a lemma about a field of a record):
--   these are matched against the eliminations of the other term, from
--   the end.
firstOrderMatch :: Int -> Set MetaId -> Term -> Term -> [(MetaId, Term)]
firstOrderMatch n ms = go
  where
    go t u = case (t, u) of
      (MetaV x es, _) | x `Set.member` ms -> case drop n es of
        []    -> [(x, u)]
        extra -> case splitElims (length extra) u of
          Just (h, es') -> (x, h) : elims extra es'
          Nothing       -> []
      (Def f es, Def f' es')     | f == f'                 -> elims es es'
      (Con c _ es, Con c' _ es') | conName c == conName c' -> elims es es'
      (Var i es, Var j es')      | i == j                  -> elims es es'
      _ -> []
    elims es es' = concat (zipWith elim es es')
    elim (Apply a) (Apply b) = go (unArg a) (unArg b)
    elim _         _         = []
    -- Split the last @k@ eliminations off a neutral term.
    splitElims k = \case
      Var j es | length es >= k -> Just $ first (Var j) (splitAt (length es - k) es)
      Def f es | length es >= k -> Just $ first (Def f) (splitAt (length es - k) es)
      _ -> Nothing

------------------------------------------------------------------------
-- * solve_by_elim
------------------------------------------------------------------------

-- | Try to close the given goals (with their remaining depth) using the
--   local variables and the constructors of their types.  Backtracks over
--   the choices; on failure the state is left as it was.
solveByElim :: IORef Int -> [(MetaId, Int)] -> TCM Bool
solveByElim _    []              = return True
solveByElim fuel ((m, d) : goals) = do
  -- A goal is closed when its solution has no open metas left; if it was
  -- instantiated by a term with metas, these metas become the goals.
  open <- openMetasOf =<< metaTerm m
  case open of
    []             -> solveByElim fuel goals
    [m'] | m' == m -> solveOpen
    ms             -> solveByElim fuel (map (, d) ms ++ goals)
  where
    solveOpen = do
      n <- liftIO $ readIORef fuel
      if d <= 0 || n <= 0 then return False else do
        goal  <- getMetaTypeInContext m
        gkey  <- goalKey goal
        heads <- (++) <$> localHeads <*> constructorHeads goal
        let heads' = [ h | h <- heads, Just{} <- [matchKey (headKey h) gkey] ]
        orM' heads' $ \ h -> attempt $ do
          liftIO $ modifyIORef' fuel (subtract 1)
          refineWith h m >>= \case
            Nothing  -> return False
            Just new -> solveByElim fuel (map (, d - 1) new ++ goals)
    orM' []       _ = return False
    orM' (x : xs) f = ifM (f x) (return True) (orM' xs f)

-- | The summary of the conclusion of a goal.
goalKey :: Type -> TCM KTree
goalKey goal = do
  TelV tel core <- telView =<< instantiateFull goal
  core <- instantiateFull core
  return $ termKey (size tel) keyDepth (unEl core)

------------------------------------------------------------------------
-- * Main loop
------------------------------------------------------------------------

librarySearch
  :: LibrarySearchMode
  -> Rewrite         -- ^ Normalisation of the solutions.
  -> InteractionId   -- ^ The hole.
  -> Range           -- ^ Range of the hole.
  -> String          -- ^ Content of the hole (currently unused).
  -> TCM LibrarySearchResult
librarySearch mode norm ii _rng _str = withInteractionId ii $ withSavedState $ do
  mi <- lookupInteractionId ii
  mv <- lookupLocalMeta mi
  case mvInstantiation mv of
    OpenMeta{} -> search mi
    _          -> return $ LibrarySearchFailed
      "The goal is already partially solved; library search only works on empty goals."
  where
  search mi = do
    scope <- getInteractionScope ii
    self  <- lookupInteractionPoint ii <&> \ ip -> case ipClause ip of
      IPClause{ ipcQName = f } -> Just f
      IPNoClause               -> Nothing
    goal  <- getMetaTypeInContext mi
    gkey  <- goalKey goal
    eq    <- getBuiltinName builtinEquality

    reportSDoc "interaction.search" 10 $ "Library search for" <+> prettyTCM goal

    -- The goal meta we refine.  It is a copy of the hole, so that the hole
    -- itself is never touched.
    (top, topTerm) <- newValueMeta DontRunMetaOccursCheck CmpLeq goal

    candidates <- libraryCandidates scope self
    let scored = sortBy (comparing (\ (h, s) -> (Down s, not (headInScope h))))
          [ (h, s)
          | h <- candidates
          , not $ isTrivialKey eq (headKey h)
          , Just s <- [matchKey (headKey h) gkey]
          ]
    reportSLn "interaction.search" 10 $ unwords
      [ show (length candidates), "candidates,", show (length scored), "after filtering" ]
    reportSDoc "interaction.search" 30 $ "Candidates:" <+>
      fsep (punctuate comma [ maybe "?" prettyTCM (headName h) | (h, _) <- scored ])

    start <- getCPUTime
    let timeUp = do
          now <- getCPUTime
          return $ now - start > fromMilliseconds searchTimeout

    -- First, as Lean, try to close the goal using the local context only.
    closedLocally <- withSavedState $ do
      fuel <- liftIO $ newIORef elimFuel
      ifM (solveByElim fuel [(top, elimDepth)])
        (Just <$> suggestion topTerm True [])
        (return Nothing)

    case (mode, closedLocally) of
      (SearchExact, Just s) -> return $ LibrarySearchExact s
      (SearchExact, Nothing) -> do
        let loop [] = return Nothing
            loop ((h, _) : hs) = ifM timeUp (return Nothing) $ do
              r <- withSavedState $ guardImpossible "exact" (headName h) $ tryExact top topTerm h
              maybe (loop hs) (return . Just) r
        loop scored <&> \case
          Just s  -> LibrarySearchExact s
          Nothing -> LibrarySearchFailed "exact? could not close the goal."
      (SearchApply, _) -> do
        let loop _ [] = return []
            loop 0 _  = return []
            loop n ((h, _) : hs) = ifM timeUp (return []) $ do
              r <- withSavedState $ guardImpossible "apply" (headName h) $ tryApply top topTerm h
              case r of
                Nothing -> loop n hs
                Just s  -> (s :) <$> loop (n - 1) hs
        sugs <- loop maxSuggestions scored
        -- Stable sort: fewer subgoals first, then specificity.
        let sugs' = maybe id (:) closedLocally $
                      sortBy (comparing (length . sugSubgoals)) sugs
        return $ if null sugs'
          then LibrarySearchFailed "apply? found no lemma whose conclusion unifies with the goal."
          else LibrarySearchApply sugs'

  tryExact top topTerm h = refineWith h top >>= \case
    Nothing -> return Nothing
    Just subgoals -> do
      fuel <- liftIO $ newIORef elimFuel
      ok <- solveByElim fuel [ (g, elimDepth) | g <- subgoals ]
      solution <- instantiateFull topTerm
      if not ok || not (null (allOpenMetas solution)) then return Nothing else
        Just <$> suggestion topTerm (headInScope h) []

  tryApply top topTerm h = refineWith h top >>= \case
    Nothing -> return Nothing
    Just subgoals -> do
      -- As in Lean: if all the subgoals can be closed, we have a complete
      -- solution; otherwise they are all left as new holes (closing only
      -- some of them could make the others unprovable).
      fuel <- liftIO $ newIORef elimFuel
      closed <- attempt $ solveByElim fuel [ (g, elimDepth) | g <- subgoals ]
      if closed
        then Just <$> suggestion topTerm (headInScope h) []
        else Just <$> suggestion topTerm (headInScope h) subgoals

  -- Print the current solution of the goal meta.
  suggestion topTerm inScope open = do
    -- The types of the subgoals are printed first: printing the solution
    -- turns its metas into interaction points.
    goals <- forM open $ \ m -> do
      -- Simplified, so that the projections of instantiated module
      -- applications (Carrier, _≈_, ...) are unfolded.
      t <- simplify =<< instantiateFull =<< getMetaTypeInContext m
      P.render <$> ("?" <+> ":" <+> prettyTCM t)
    v <- normalForm norm =<< instantiateFull topTerm
    e <- locallyTC ePrintMetasBare (const True) $ blankNotInScope =<< reify v
    str <- P.render <$> prettyTCM e
    return LibrarySuggestion
      { sugExpr     = str
      , sugSubgoals = goals
      , sugInScope  = inScope
      }

  allOpenMetas :: Term -> [MetaId]
  allOpenMetas = allMetas (: [])
