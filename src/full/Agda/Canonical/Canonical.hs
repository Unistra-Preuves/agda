-- | Proof search with Canonical (@C-c C-g@).
--
--   The pipeline:
--
--   * the options written in the hole are parsed ("Agda.Canonical.Options"),
--     and the lemmas resolved ("Agda.Canonical.Lemma");
--
--   * what Agda knows of the hole is gathered ("Agda.Canonical.Hole"), and
--     the goal translated ("Agda.Canonical.ToCanonical");
--
--   * Canonical solves it through "Agda.Canonical.FFI" ('search'), and the
--     solutions are printed in Agda syntax ("Agda.Canonical.FromCanonical");
--
--   * unless @+debug@ is given, the first solution accepted by Agda is
--     written in the file ("Agda.Canonical.Write").
--
--   With @count := n@ (n > 1), if several solutions are accepted by Agda,
--   nothing is written: they are returned ('CanonicalChoose') for the user
--   to choose one, which 'pickCanonical' then writes.

module Agda.Canonical.Canonical
  ( callCanonical
  , pickCanonical
  ) where

import Control.Monad (forM, guard)
import Control.Monad.Except (catchError)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.List qualified as List
import Data.List (nub)
import Data.Map qualified as Map
import Data.Maybe (isJust, isNothing, listToMaybe, mapMaybe)
import Data.Set qualified as Set

import Agda.Canonical.Cubical (isCubical)
import Agda.Canonical.FFI (runCanonical)
import Agda.Canonical.FromCanonical
import Agda.Canonical.Hole
import Agda.Canonical.Induction (CallMatrix, compatibleSubset, corecursiveCalls, inductionHypotheses, isGuarded, terminateTogether)
import Agda.Canonical.Interval (normaliseIntervals)
import Agda.Canonical.Lemma (hintNames, lemmaName, moduleHints)
import Agda.Canonical.Options
import Agda.Canonical.Params (droppedParams)
import Agda.Canonical.Recursor (withoutIHs)
import Agda.Canonical.ToCanonical (produceCanonicalGoal, undeclaredSymbols)
import Agda.Canonical.Types
import Agda.Canonical.Utils (etaTo, freshString, metaVarName, nameToString)
import Agda.Canonical.Write (giveTerm, writeFields, writeSolution)
import Agda.Interaction.Base (Rewrite, UseForce(..))
import Agda.Interaction.BasicOps (give, parseExprIn)
import Agda.Syntax.Builtin (PrimitiveId (..), builtinIOne, builtinIZero)
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty qualified as P
import Agda.Syntax.Internal
import Agda.Syntax.Internal.MetaVars (noMetas)
import Agda.Syntax.Position (Range)
import Agda.Syntax.Scope.Base (isNameInScope)
import Agda.Syntax.Translation.AbstractToConcrete (abstractToConcrete_)
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Builtin (getBuiltinName', getPrimitiveName')
import Agda.TypeChecking.Monad.Context (getContextArgs, getContextTelescope)
import Agda.TypeChecking.Monad.MetaVars
import Agda.TypeChecking.Monad.Signature (HasConstInfo (getConstInfo))
import Agda.TypeChecking.Monad.State (getScope)
import Agda.TypeChecking.Pretty (prettyTCM)
import Agda.TypeChecking.Reduce (instantiateFull)
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.List (headWithDefault)

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

-- | Writes the solution of the given number (counted from 1) among the
--   ones left for the user to choose.
pickCanonical :: CanonicalChoices -> Int -> TCM CanonicalResult
pickCanonical cc k = case drop (k - 1) (ccSolutions cc) of
  sol : _ | k >= 1 -> writeSolution False True (ccGoal cc) (ccRange cc) (ccInfo cc) [sol]
  _ -> return . CanonicalMessage $ "Canonical: there is no solution " ++ show k

---------------------------------------------------------------------------
-- * Search
---------------------------------------------------------------------------

-- | Translates the goal, calls Canonical, and displays or writes the solutions.
--   With @hcomp@ among the lemmas, a hole with a cubical boundary is first
--   tried as an @hcomp@ over that boundary (see 'hcompSkeleton').
solve :: Bool -> InteractionId -> Range -> CanonicalOptions -> [QName] -> TCM CanonicalResult
solve split ii rng opts lemmas = do
  sk <- hcompSkeleton ii rng opts lemmas
  case sk of
    Just (Right res) -> return res
    Just (Left report) | optDebug opts -> do
      plain <- solvePlain split ii rng opts lemmas
      return . CanonicalMessage $ report ++ case plain of
        CanonicalMessage m -> "\n\n--- Without the skeleton :\n" ++ m
        _                  -> ""
    _ -> solvePlain split ii rng opts lemmas

-- | The condition on the base of an @hcomp@, @φ ⊢ u i0 = a@, is checked by
--   Agda when it elaborates an application of @hcomp@; Canonical cannot
--   state it when @φ@ mentions the variables of the context (it would have
--   to substitute them in @u@ and @a@).  Searching @hcomp@ as a lemma would
--   then give any base, which Agda rejects.
--
--   So when @hcomp@ is a lemma and the hole has a cubical boundary, the
--   hole is first given, in a saved state, the skeleton of a filler: an
--   @hcomp@ over the faces of the boundary, with a hole in each clause of
--   the system and for the base,
--
--   > hcomp (λ k → λ { (i = i0) → ? ; (i = i1) → ? ; (j = i0) → ? ; … }) ?
--
--   Agda elaborates it, and its constraints on the new holes state the
--   condition on the base exactly (as constraints on a face, see
--   'Agda.Canonical.Hole.faceConstraints'), with the agreement of the
--   clauses on their overlaps and the boundary of the hole.  These holes are found together (the
--   constraints link them, see 'produceCanonicalGoal'), from the first
--   clause; the values are read back, the state is restored, and the
--   complete @hcomp@ is given to the hole.
--
--   'Nothing' when the skeleton does not apply or Agda rejects it (e.g. a
--   variable of a face, @i0@ or @i1@ cannot be written at the hole);
--   @Left@ the reason (or the @+debug@ report) when it gives no solution.
hcompSkeleton :: InteractionId -> Range -> CanonicalOptions -> [QName] -> TCM (Maybe (Either String CanonicalResult))
hcompSkeleton ii rng opts lemmas = do
  cub <- isCubical
  mhc <- getPrimitiveName' PrimHComp
  bds <- holeBoundary ii
  ops <- enclosingOps ii
  case mhc of
    Just hc | cub, hc `elem` lemmas, not (null bds), hc `notElem` ops -> do
      mtext <- skeletonText ii hc bds
      case mtext of
        Nothing -> return Nothing
        Just sk -> do
          st   <- getTC
          ids0 <- map fst <$> getInteractionIdsAndMetas
          given <- (True <$ (give WithoutForce ii =<< parseExprIn ii rng sk))
                     `catchError` \ _ -> return False
          ids <- filter (`notElem` ids0) . map fst <$> getInteractionIdsAndMetas
          r <- case ids of
            target : _ | given, length ids == length bds + 1 -> do
              trng <- getInteractionRange target
              let opts' = opts { optCount = 1 }
                  lemmas' = filter (/= hc) lemmas
              res <- solvePlain False target trng opts' lemmas'
              case res of
                CanonicalMessage m
                  | optDebug opts -> return . Just . Left $
                      "--- hcomp skeleton :\n" ++ sk ++ "\n\n" ++ m
                  | otherwise -> return (Just (Left m))
                CanonicalGive t -> do
                  -- The other holes have been assigned by
                  -- 'Agda.Canonical.Write.assignMetas'.
                  others <- mapM holeValue (drop 1 ids)
                  return . Just . Right $ fillSkeleton bds sk (Just t : others)
                _ -> return Nothing
            _ -> return Nothing
          putTC st
          case r of
            Just (Right (Just filled)) -> do
              g <- giveTerm ii rng filled filled
              return . Just $ either (Left . fst) Right g
            Just (Right Nothing) -> return Nothing
            Just (Left m) -> return (Just (Left m))
            Nothing -> return Nothing
    _ -> return Nothing
  where
    -- The value of a hole, printed in its context, if it is solved.
    holeValue :: InteractionId -> TCM (Maybe String)
    holeValue i = withInteractionId i $ do
      m <- lookupInteractionId i
      v <- instantiateFull . MetaV m . map Apply =<< getContextArgs
      if not (noMetas v) then return Nothing else Just . P.render <$> prettyTCM v
    -- The skeleton with its holes, in order, replaced by their values
    -- (printed at the precedence of their holes: the base, an argument, is
    -- parenthesised).
    fillSkeleton :: [a] -> String -> [Maybe String] -> Maybe String
    fillSkeleton faces sk vals = do
      vs <- sequence vals
      guard (length vs == length faces + 1)
      return (go sk vs)
      where
        go ('?' : rest) (v : more) = v ++ go rest more
        go (c : rest) more         = c : go rest more
        go [] _                    = []

-- | The text of the skeleton of 'hcompSkeleton' at the hole: @hcomp@,
--   @i0@, @i1@ and the variables of the faces as written there, with a
--   fresh name for the variable of the composition.  'Nothing' if one of
--   them cannot be written (the skeleton is then also rejected by the
--   scope checker, but this saves the attempt).
skeletonText :: InteractionId -> QName -> [([(Term, Bool)], Term)] -> TCM (Maybe String)
skeletonText ii hc bds = withInteractionId ii $ do
  mi0 <- getBuiltinName' builtinIZero
  mi1 <- getBuiltinName' builtinIOne
  scope <- getScope
  let written q = if isNameInScope q scope then Just . P.prettyShow <$> abstractToConcrete_ q
                  else return Nothing
  hcN <- written hc
  i0N <- maybe (return Nothing) written mi0
  i1N <- maybe (return Nothing) written mi1
  -- The names of the context, the innermost first (de Bruijn order).
  names <- reverse . map (fst . unDom) . telToList <$> getContextTelescope
  let
      var k = case drop k names of
        x : _ | x /= "_", take 1 x /= "." -> Just x
        _                                 -> Nothing
      k = headWithDefault __IMPOSSIBLE__ [ v | n <- [0 :: Int ..], let v = "k" ++ replicate n '\'', v `notElem` names ]
  return $ do
    hcS <- hcN; i0S <- i0N; i1S <- i1N
    faces <- forM bds $ \ (face, _) -> do
      conds <- forM face $ \case
        (Var a [], b) -> do x <- var a; return ("(" ++ x ++ " = " ++ (if b then i1S else i0S) ++ ")")
        _             -> Nothing
      guard (not (null conds))
      return (unwords conds)
    return $ hcS ++ " (λ " ++ k ++ " → λ { "
      ++ List.intercalate " ; " [ f ++ " → ?" | f <- faces ] ++ " }) ?"

-- | 'solve' without the skeleton of 'hcompSkeleton'.
solvePlain :: Bool -> InteractionId -> Range -> CanonicalOptions -> [QName] -> TCM CanonicalResult
solvePlain split ii rng opts lemmas = do
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
  cons0 <- concat <$> sequence
             [ solvedValue inMeta mv, metaConstraints inMeta, otherBoundaries inMeta ii ]
  cons <- unblockTwins cons0
  -- The metas solved since the goal was created are instantiated.  The type
  -- is a Π-type over the context.
  ty   <- instantiateFull =<< getMetaTypeInContext mv
  ctx  <- inMeta $ instantiateFull =<< getContextTelescope
  self <- maybe "rec" nameToString <$> holeFunction ii
  hyps <- inHole $ hypotheses (inductionHypotheses ii) self
  lets <- inHole letVariables
  ops  <- enclosingOps ii
  let -- The goal with the hypotheses @hs@, its information, and its 'guardCalls'.
      prepare hs = do
        (g, i0) <- produceCanonicalGoal (nub (lemmas ++ ops)) ctx
                     ([ (n, t, Nothing) | (n, t, _, _) <- hs ] ++ [ (n, t, Just v) | (n, t, v) <- lets ])
                     ty bds (mv, cons)
        i <- completeInfo ii self pre [ (n, h) | (n, _, h, _) <- hs ] i0
        (g, i,) <$> guardCalls [ n | (n, _, _, m) <- hs, isGuarded m ] i g
      matrices hs = [ (n, m) | (n, _, _, m) <- hs ]
  (goal, info, guardedGoal) <- prepare hyps
  found <- search opts info (matrices hyps) guardedGoal
  -- Without solution, a human would split a coinductive result into its fields.
  rhs <- (split &&) <$> holeIsRHS ii
  coinductive <- if rhs && isNothing retarget && isNothing (giCont info)
                 then isJust <$> fieldsGoal info goal else return False
  byFields <- case found of
    Right (_, _, []) | coinductive -> do
      calls <- withInteractionId ii $ hypotheses (corecursiveCalls ii) self
      let hyps2 = hyps ++ calls
      (_, info2, guarded) <- prepare hyps2
      fieldsGoal info2 guarded >>= \case
        Nothing -> return Nothing
        Just wrapped -> do
          r <- search opts info2 (matrices hyps2) wrapped
          return $ case r of
            Right (_, _, _ : _) -> Just (hyps2, r)
            _                   -> Nothing
    _ -> return Nothing
  -- The definitions out of scope at the hole, which the solutions cannot
  -- name: folded into definitions in scope where possible.
  scope <- withInteractionId ii getScope
  let folded (goal', info0', results0) = (goal', foldInfo info0', results)
        where
          oos     = Set.fromList [ n | (n, q) <- Map.toList (giDefs info0'), not (isNameInScope q scope) ]
          fold    = foldOutOfScope oos info0'
          results = [ (fold e, [ (m, fold v) | (m, v) <- vals ]) | (e, vals) <- results0 ]
  case (byFields, found) of
    (Just (hyps2, Right r), _)
      | optDebug opts -> return . CanonicalMessage $ debugReport goal' info' hyps2 results
      | otherwise     -> writeFields ii rng info' results
      where (goal', info', results) = folded r
    (_, Left err) -> return $ CanonicalMessage err
    (_, Right r)
      | optDebug opts -> return . CanonicalMessage $ debugReport goal' info' hyps results
      | otherwise     -> writeSolution (optCount opts > 1) split ii rng info' results
      where (goal', info', results) = folded r

-- | The goal of a human who splits a coinductive result into its fields
--   (@C-c C-c@ without variables on @repeat a = ?@), in the format of Canonical:
--   for @Stream A@ with the fields @head : A@ and @tail : Stream A@,
--
--   > (k : (head : A) (tail : Stream A) → Fields) → Fields
--
--   whose only solutions are @λ k → k h t@, for @Fields@ is only returned by
--   @k@.  'Nothing' if the goal is not such a record, fully applied to
--   first-order parameters (the constructor is declared with the record).
fieldsGoal :: GoalInfo -> CDecl -> TCM (Maybe CDecl)
fieldsGoal info goal = case typ goal of
  Just e@(CExpr [] ctx (CSpine r as)) | Just q <- Map.lookup r (giDefs info) ->
    theDef <$> getConstInfo q >>= \case
      RecordDefn rd | _recInduction rd == Just CoInductive
                    , Just n <- ctorName (conName (_recConHead rd))
                    , CExpr ps _ _ : _ <- [ t | x <- ctx, name x == n, Just t <- [typ x] ]
                    , length as <= length ps, all (null . params) as -> do
        g <- freshString "Fields"
        k <- freshString "k"
        let (pars, fields) = splitAt (length as) ps
            sub    = Map.fromList (zip (map name pars) as)
            subD d = d { typ = substExpr sub <$> typ d }
            res    = simpleSpine g
        return $ Just goal { typ = Just e { params = [ typed k (CExpr (map subD fields) [] res) ]
                                          , lets   = untyped g : ctx
                                          , spine  = res } }
      _ -> return Nothing
  _ -> return Nothing
  where
    ctorName c = listToMaybe [ n | (n, q) <- Map.toList (giDefs info), q == c ]

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
--   not terminate is rejected when it is given ('Agda.Canonical.Write.tryGive').
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

-- | What a human knows of a corecursive call: its result may not be projected
--   (@tail (from n) = from n .tail@), nor passed to the function being defined
--   (@tail (dup s) = dup (dup s)@): Agda's termination checker rejects them.
--
--   In the format of Canonical, which never builds a redex: these terms are
--   the left-hand sides of rules, whose right-hand side is an untyped symbol
--   that nothing is equal to.
guardCalls :: [String] -> GoalInfo -> CDecl -> TCM CDecl
guardCalls [] _ goal = return goal
guardCalls hs info goal = case typ goal of
  Nothing -> return goal
  Just e  -> do
    bad <- freshString "Unguarded"
    let ctx    = lets e
        calls  = [ d | d <- ctx, name d `elem` hs ]
        names  = Map.fromList [ (q, n) | (n, q) <- Map.toList (giDefs info) ]
        arity  = maybe [] (map (maybe 0 (length . params) . typ) . params) . typ
        wild a = etaTo a . simpleExpr =<< freshString "w"
        -- A call on any arguments.
        call d = CExpr [] [] . CSpine (name d) <$> mapM wild (arity d)
        rule h as = CEquation (CSpine h as) (simpleSpine bad) True
    projected <- fmap concat $ forM calls $ \ d -> do
      fields <- case typ d of
        Just (CExpr _ _ (CSpine r _)) | Just q <- Map.lookup r (giDefs info) ->
          theDef <$> getConstInfo q <&> \case
            RecordDefn rd -> map unDom (_recFields rd)
            _             -> []
        _ -> return []
      fmap concat $ forM fields $ \ f -> case Map.lookup f names of
        Just p | [pd] <- [ x | x <- ctx, name x == p ] -> do
          pars <- droppedParams . theDef <$> getConstInfo f
          let (before, after) = splitAt pars (arity pd)
          as  <- mapM wild before
          c   <- call d
          bs  <- mapM wild (drop 1 after)
          return [ (p, rule p (as ++ [c] ++ bs)) | length after >= 1 ]
        _ -> return []
    nested <- fmap concat $ forM calls $ \ d ->
      fmap concat $ forM (zip [0 ..] (arity d)) $ \ (i, a) ->
        if a /= 0 then return [] else fmap concat $ forM calls $ \ d' -> do
          as <- mapM wild (arity d)
          c  <- call d'
          -- Only where the result of the call has the type of the argument.
          let fits = case (typ d, typ d') of
                (Just (CExpr ps _ _), Just (CExpr _ _ (CSpine r _))) ->
                  case typ (ps !! i) of
                    Just (CExpr [] _ (CSpine r' _)) -> r == r'
                    _                               -> False
                _ -> False
          return [ (name d, rule (name d) (take i as ++ [c] ++ drop (i + 1) as)) | fits ]
    let eqs = Map.fromListWith (flip (++)) [ (h, [q]) | (h, q) <- projected ++ nested ]
        add d = d { equations = equations d ++ Map.findWithDefault [] (name d) eqs }
    return goal { typ = Just e { lets = untyped bad : map add ctx } }
