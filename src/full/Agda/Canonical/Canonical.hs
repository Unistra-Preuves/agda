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
--     receives its right-hand side, with real recursive calls;
--
--   * otherwise the hole is filled with the term, first without implicit
--     arguments, then, if this leaves unsolved metas or constraints, with
--     all implicit arguments given in braces.

module Agda.Canonical.Canonical
  ( callCanonical
  ) where

import Control.Monad (forM)
import Control.Monad.Except (catchError)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Monad.State (State, evalState, get, put)
import Data.IntMap qualified as IntMap
import Data.List (findIndex)
import Data.Map qualified as Map
import Data.Maybe (isJust)
import Data.Set qualified as Set

import Agda.Canonical.FFI (runCanonical)
import Agda.Canonical.FromCanonical
import Agda.Canonical.Options
import Agda.Canonical.ToCanonical (produceCanonicalGoal)
import Agda.Canonical.Types
import Agda.Canonical.Utils (nameToString)
import Agda.Interaction.Base (Rewrite, UseForce(..))
import Agda.Interaction.BasicOps (give, parseExprIn)
import Agda.Interaction.MakeCase (makeCase, makeCaseIntro)
import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty qualified as P
import Agda.Syntax.Concrete.Name qualified as C
import Agda.Syntax.Info (patNoRange)
import Agda.Syntax.Internal
import Agda.Syntax.Position (Range)
import Agda.Syntax.Scope.Monad (freshAbstractName_)
import Agda.TypeChecking.Errors (prettyError)
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Constraints (getAllConstraints)
import Agda.Syntax.Translation.AbstractToConcrete (abstractToConcrete_)
import Agda.TypeChecking.Monad.Context (getContext, getContextArgs, getContextTelescope)
import Agda.TypeChecking.Telescope (flattenContext)
import Agda.TypeChecking.Monad.MetaVars
import Agda.TypeChecking.Substitute

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
        []  -> liftTCM $ solve split ii rng opts [ q | (_, Just q) <- lemmas ]
        bad -> return . CanonicalMessage $
          "Canonical: these lemmas are not names of definitions: " ++ unwords bad

-- | The definition named by a lemma: a function, a postulate, a datatype,
--   a constructor or a projection.
lemmaName :: A.Expr -> Maybe QName
lemmaName e = case e of
  A.ScopedExpr _ e' -> lemmaName e'
  A.Def' q _        -> Just q
  A.Con c           -> Just (A.headAmbQ c)
  A.Proj _ p        -> Just (A.headAmbQ p)
  _                 -> Nothing

-- | Translates the goal, calls Canonical, and displays or writes the solutions.
solve :: Bool -> InteractionId -> Range -> CanonicalOptions -> [QName] -> TCM CanonicalResult
solve split ii rng opts lemmas = do
  -- Cubical boundary of the goal (not used by the translation yet).
  bds <- withInteractionId ii $ do
    ip <- lookupInteractionPoint ii
    as <- getContextArgs
    let go (im, r) = do
          eqns <- forM (IntMap.toList im) $ \ (a, b) -> return (Var a [], b)
          return (eqns, r `apply` as)
    traverse go (Map.toList . getBoundary $ ipBoundary ip)
  ty  <- getMetaTypeInContext =<< lookupInteractionId ii
  ctx <- withInteractionId ii getContextTelescope
  -- Name of the function containing the hole, for the recursive calls.
  self <- do
    ip <- lookupInteractionPoint ii
    return $ case ipClause ip of
      IPClause { ipcQName = q } -> nameToString q
      IPNoClause                -> "rec"
  (goal, info0) <- produceCanonicalGoal lemmas ctx ty bds
  -- Context variables the user cannot refer to (shown "not in scope").
  outOfScope <- withInteractionId ii $ do
    vars <- flattenContext <$> getContext
    fmap concat $ forM vars $ \ (CtxVar x _) -> do
      c <- abstractToConcrete_ x
      return [ P.prettyShow (nameConcrete x) | C.isInScope c == C.NotInScope ]
  let info = info0 { giOutOfScope = outOfScope }
  results <- liftIO $ runCanonical goal (optTimeout opts) (optCount opts)
  let decls = maybe [] lets (typ goal)
      pp    = cexprToAgda False info decls self
  if optDebug opts then
    return . CanonicalMessage $ show goal ++ "\n\n" ++ case results of
      []  -> "No solution found."
      [d] -> "--- Hint :\n" ++ pp d
      ds  -> "--- Hints :\n" ++ unlines [ show i ++ ". " ++ pp d | (i, d) <- zip [1 :: Int ..] ds ]
  else writeSolution split ii rng info decls self results

---------------------------------------------------------------------------
-- * Writing a solution
---------------------------------------------------------------------------

-- | Writes the first solution accepted by Agda.
writeSolution
  :: Bool           -- ^ May the clause be split?
  -> InteractionId  -- ^ The goal.
  -> Range          -- ^ Its range.
  -> GoalInfo       -- ^ Information about the goal.
  -> [CDecl]        -- ^ The context sent to Canonical.
  -> String         -- ^ Name of the function containing the hole.
  -> [CExpr]        -- ^ The solutions.
  -> TCM CanonicalResult
writeSolution _ _ _ _ _ _ [] = return CanonicalNoResult
writeSolution split ii rng info decls self sols = go [] sols
  where
    go errs [] = return . CanonicalMessage $
      "Canonical found solutions, but Agda rejected them:\n" ++ unlines (reverse errs)
    go errs (d : ds) = do
      msplit <- case canonicalSplit info decls self d of
        Just sp | split -> splitClause ii rng sp
        _               -> return Nothing
      case msplit of
        Just res -> return res
        Nothing  -> do
          r <- giveTerm ii rng (cexprToAgda False info decls self d)
                               (cexprToAgda True  info decls self d)
          either (\ err -> go (err : errs) ds) return r

-- ** Terms

-- | Fills the hole with the first expression, or with the second one (the
--   same with implicit arguments) if the first one leaves unsolved metas or
--   constraints.  If both are rejected or leave something unsolved, the
--   state is restored and the reason is returned.
giveTerm :: InteractionId -> Range -> String -> String -> TCM (Either String CanonicalResult)
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
    failed r = return . Left $ s1 ++ "\n    " ++ case r of
      Left err -> err
      Right _  -> "leaves unsolved metas or constraints"

-- | Gives an expression.  Returns whether no new meta or constraint is left
--   unsolved, or the error message.
tryGive :: InteractionId -> Range -> String -> TCM (Either String Bool)
tryGive ii rng s = do
  ms0 <- getOpenMetas
  cs0 <- length <$> getAllConstraints
  r <- (Right <$> (give WithoutForce ii =<< parseExprIn ii rng s))
         `catchError` \ err -> Left . P.render <$> prettyError err
  case r of
    Left err -> return (Left err)
    Right _  -> do
      ms1 <- getOpenMetas
      cs1 <- length <$> getAllConstraints
      return (Right (all (`elem` ms0) ms1 && cs1 <= cs0))

-- ** Case splits

-- | Splits the clause of the hole, and fills the new clauses.
--   'Nothing' if Agda cannot split there, or if the clauses produced by the
--   split do not have the expected shape.
splitClause :: InteractionId -> Range -> Split -> TCM (Maybe CanonicalResult)
splitClause ii rng sp = (`catchError` \ _ -> return Nothing) $ do
  ip <- lookupInteractionPoint ii
  let origPats = case ipClause ip of
        IPClause { ipcClause = cl } -> Just (A.spLhsPats (A.clauseLHS cl))
        IPNoClause                  -> Nothing
  case (origPats, spTarget sp) of
    -- Split on a pattern variable of the clause.
    (Just ops, SplitVar x) | Just i <- findIndex (isVarP x . namedArg) ops -> do
      (f, casectxt, cs) <- makeCase ii rng x
      finish f casectxt (const (Just i)) (const []) cs
    -- Introduce the arguments of the goal, and split on the k-th one.  The
    -- introduced explicit arguments follow the explicit patterns of the
    -- clause; the implicit ones are not written.
    (Just ops, SplitArg k hs) | k < length hs, visible (hs !! k) -> do
      (f, casectxt, cs) <- makeCaseIntro ii rng k
      let e0       = length (filter visible ops)
          visPos t = e0 + length (filter visible (take t hs))
          nthVisible ps n = case drop n [ j | (j, q) <- zip [0 ..] ps, visible q ] of
            j : _ -> Just j
            []    -> Nothing
          params ps = [ if visible h then nthVisible ps (visPos t) >>= varName . namedArg . (ps !!)
                        else Nothing
                      | (t, h) <- zip [0 ..] hs ]
      finish f casectxt (\ ps -> nthVisible ps (visPos k)) params cs
    _ -> return Nothing
  where
    isVarP x p = case p of
      A.VarP b -> P.prettyShow (A.unBind b) == x
      _        -> False
    finish f casectxt pos params cs
      | isJust casectxt = return Nothing
      | otherwise       = do
          mcs <- mapM (fillClause sp pos params) cs
          return $ CanonicalMakeCase f <$> sequence mcs

-- | Fills a clause produced by a split: binds the fields that the
--   right-hand side needs, and computes the right-hand side.
--   Absurd clauses are kept as they are.
fillClause
  :: Split
  -> ([NamedArg A.Pattern] -> Maybe Int)            -- ^ Position of the split pattern.
  -> ([NamedArg A.Pattern] -> [Maybe String])       -- ^ Names of the introduced arguments.
  -> A.Clause
  -> TCM (Maybe (A.Clause, Maybe String))
fillClause sp pos params cl = case A.lhsCore lhs of
  core@A.LHSHead{ A.lhsPats = ps0 }
    | let ps = uniquePatVars ps0, Just i <- pos ps, i < length ps -> case namedArg (ps !! i) of
    A.AbsurdP{} -> return (Just (cl, Nothing))
    A.ConP ci c sub
      | (br : _) <- [ b | b <- spBranches sp, sbCtor b == nameToString (A.headAmbQ c) ] -> do
          let taken = concatMap (patVars . namedArg) ps
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
          new  = case [ n | n <- base : [ base ++ map subscript (show k) | k <- [1 :: Int ..] ]
                          , n `Set.notMember` used ] of
            n : _ -> n
            []    -> base
      put (Set.insert new used)
      return (A.BindName x { A.nameConcrete = C.simpleName new })
    subscript c = toEnum (fromEnum c - fromEnum '0' + fromEnum '₀')

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
      q : qs' | visible q == visible h, isJustNot (bareNameOf q) -> case namedArg q of
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
    isJustNot    = not . isJust
    bindName     = P.prettyShow . A.unBind
    -- Is an implicit field after this one, in the same run of implicit
    -- fields, used?
    laterUsed (_ : rest) = any (\ (_, _, u) -> u) (takeWhile (\ (_, h, _) -> not (visible h)) rest)
    laterUsed []         = False

    freshVar taken x = do
      let n = head' [ y | y <- iterate (++ "'") x, y `Set.notMember` taken ]
      a <- freshAbstractName_ (C.simpleName n)
      return (A.mkBindName a, Set.insert n taken)
    head' (y : _) = y
    head' []      = "x"
