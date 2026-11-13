-- | Writing a solution of Canonical in the file.
--
--   The first solution accepted by Agda is written:
--
--   * if it is a recursor applied to a variable of the context, the clause
--     is split on that variable (as with @C-c C-c@) and each new clause
--     receives its right-hand side, with real recursive calls; the hidden
--     variables that the right-hand sides use are made visible
--     (@comp {p = p} refl = p@);
--
--   * otherwise the hole is filled with the term, first without implicit
--     arguments, then, if this leaves unsolved metas or constraints, with
--     all implicit arguments given in braces.  The term is written in the
--     clause rather than given when it is a λ or when it uses variables
--     that the user cannot refer to (see 'giveSolution').
--
--   The metas of the goal are first assigned the values found by Canonical
--   ('assignMetas').

module Agda.Canonical.Write
  ( writeSolution
  , writeFields
  , giveTerm
  ) where

import Control.Monad (forM)
import Control.Monad.Except (catchError)
import Control.Monad.State (State, evalState, get, put)
import Data.List (findIndex, nub)
import Data.Maybe (catMaybes, fromMaybe, isJust, isNothing, listToMaybe)
import Data.Set qualified as Set

import Agda.Canonical.FromCanonical
import Agda.Canonical.Hole (holeIsRHS)
import Agda.Canonical.Types
import Agda.Canonical.Utils (metaVarName)
import Agda.Interaction.Base (UseForce(..))
import Agda.Interaction.BasicOps (give, parseExprIn)
import Agda.Interaction.MakeCase (makeCase, makeCaseIntro)
import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty qualified as P
import Agda.Syntax.Concrete.Name qualified as C
import Agda.Syntax.Info (patNoRange)
import Agda.Syntax.Internal
import Agda.Syntax.Position (Range)
import Agda.Syntax.Scope.Base (scopePrecedence)
import Agda.Syntax.Scope.Monad (freshAbstractName_)
import Agda.TypeChecking.Conversion (equalTerm)
import Agda.TypeChecking.Errors (prettyError)
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Constraints (getAllConstraints)
import Agda.TypeChecking.Monad.MetaVars
import Agda.TypeChecking.Pretty (prettyTCM)
import Agda.TypeChecking.Reduce (instantiateFull)
import Agda.TypeChecking.Rules.Term (checkExpr)
import Agda.TypeChecking.Substitute
import Agda.Utils.List (headWithDefault)
import Agda.Utils.Suffix (toSubscriptDigit)

---------------------------------------------------------------------------
-- * Solutions
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

-- | Writes a solution @λ k → k h t@ of 'Agda.Canonical.Canonical.fieldsGoal'
--   as the clauses of a split on the result.  As the other rewritten
--   clauses, they are checked when the file is reloaded.
writeFields :: InteractionId -> Range -> GoalInfo -> [(CExpr, [(MetaId, CExpr)])] -> TCM CanonicalResult
writeFields ii rng info sols = (`catchError` \ _ -> return CanonicalNoResult) $ do
  (f, casectxt, cs) <- makeCase ii rng ""
  case [ es | (CExpr [_] _ (CSpine _ es), _) <- sols, length es == length cs ] of
    es : _ | isNothing casectxt ->
      return $ CanonicalMakeCase f (zip cs (map (Just . cexprToAgda False info) es))
    _ -> return CanonicalNoResult

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
          long  e = cexprToAgdaLong e info (metaVarName m) v
      st <- getTC
      -- Without, then with implicit arguments, then without η-contraction
      -- (@λ i → q i@ rather than the path @q@, against @(i : I) → A@).
      r <- firstRight st [ assign m s | s <- nub [shown False, shown True, long False, long True] ]
      case r of
        Right () -> return []
        Left err -> do
          putTC st
          return ["cannot assign _" ++ show (metaId m) ++ " := " ++ shown False ++ ": " ++ err]

    firstRight _ [] = return (Left "")
    firstRight st (a : as) = a >>= \case
      Right () -> return (Right ())
      Left err | null as   -> return (Left err)
               | otherwise -> putTC st >> firstRight st as

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
