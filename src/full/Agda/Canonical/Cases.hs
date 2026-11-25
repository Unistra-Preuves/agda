-- | Case analyses of the goal on its variables, with a motive already
--   found.
--
--   The recursor @D.rec@ of "Agda.Canonical.Recursor" leaves Canonical to
--   find the motive, a function of the indices and of the eliminated value
--   only.  Two things are then out of reach:
--
--   * the variables that depend on the eliminated one cannot be
--     generalised: eliminating @p : x ≡ y@ when @q : y ≡ z@ is in the
--     context needs the motive @λ a t → (q : a ≡ z) → C@, a Π-type that
--     Canonical does not build (Agda's case split substitutes @y := x@ in
--     the whole context instead);
--
--   * the motive itself must be searched as a term, which takes long as
--     soon as eliminations are nested, although it is almost always the
--     goal with the indices and the eliminated value abstracted.
--
--   So for each variable @x : D pars is@ of the context whose indices @is@
--   are distinct variables, the goal gets a lemma that is the case
--   analysis on @x@ with that motive, generalised over the variables @Δ@
--   that depend on @is@ or @x@ and over the binders @gs@ of the goal:
--
--   > case : (minor_c : (fs : Φ_c) (Δ_c) (gs_c : Θ_c) → G_c)… (gs : Θ) → G
--
--   where @Δ_c@, @Θ_c@ and @G_c@ are @Δ@, @Θ@ and @G@ with
--   @is := js_c@ (the indices of the constructor) and @x := c pars fs@.
--   The minor premises are stated as Π-types of Canonical: nothing needs
--   to be searched but their bodies.
--
--   The case analyses of the goals of the minor premises are declared too,
--   up to a depth: they take the binders of the minor premise first (see
--   'CaseInfo').  In @Σ-≡ p q@, the goal of the analysis on
--   @q : transport B p b ≡ b'@ has an analysis on @p@.
--
--   An answer that uses a case analysis is written with the recursor of the
--   datatype applied to the motive, the dependent variables and the binders
--   of the goal ('restoreCases'), which "Agda.Canonical.FromCanonical"
--   prints as a pattern-matching lambda, or as a case split of the clause.

module Agda.Canonical.Cases
  ( caseAnalyses
  , restoreCases
  ) where

import Control.Monad (foldM, forM)
import Data.List (nub)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe, isNothing)
import Data.Set qualified as Set

import Agda.Canonical.Eta (unfoldHead)
import Agda.Canonical.FromCanonical (Branch (..), RecInfo (..), recInfos)
import Agda.Canonical.Types
import Agda.Canonical.Utils (etaTo, etaVar, freshString)
import Agda.Syntax.Common (Hiding (..))
import Agda.TypeChecking.Monad.Base (TCM)

-- | The depth of the nested case analyses.
caseDepth :: Int
caseDepth = 2

-- | The maximal number of case analyses declared for a goal.
maxCases :: Int
maxCases = 48

-- | A goal in which case analyses are looked for.
data Problem = Problem
  { prLead  :: [CDecl]
      -- ^ The binders of the minor premises around it.
  , prVars  :: [CDecl]
      -- ^ The variables that can be eliminated or generalised, in order.
  , prGPars :: [CDecl]
      -- ^ The binders of the goal.
  , prGoal  :: CSpine
      -- ^ The goal.
  }

-- | Declares the case analyses of a goal declared directly (not through a
--   continuation).
caseAnalyses :: GoalInfo -> CDecl -> TCM (CDecl, GoalInfo)
caseAnalyses info goal = case typ goal of
  Just e | isNothing (giCont info), null (giRefold info) -> do
    let ctx    = lets e
        recs   = recInfos ctx
        decls  = Map.fromList [ (name d, d) | d <- ctx ]
        -- The datatypes whose recursor is declared, and whose constructors
        -- have no boundary (higher inductive types are left out).
        byData = Map.fromList
          [ (dn, (rn, ri, ctors))
          | (rn, ri) <- Map.toList recs
          , let dn = take (length rn - length (".rec" :: String)) rn
          , Just ctors <- [mapM ((`Map.lookup` decls) . brCtor) (riBranches ri)]
          , all (null . equations) ctors ]
        -- The variables of the context, and the fields of those of a record
        -- type (see "Agda.Canonical.Eta").
        plain d = (name d `elem` giNames info || Map.member (name d) (etaFields (giEta info)))
               && null (equations d)
               && Map.notMember (name d) (giHyps info) && not (null (typ d))
        top = Problem [] (filter plain ctx) (params e) (spine e)
    levels <- generate byData (unfoldHead ctx) caseDepth top
    -- Canonical tries the declarations of the context from the last one:
    -- the case analyses of the goal come last, the one on its first
    -- variable (the one a human splits first) at the very end; the
    -- nested ones come before them.
    let cases = case levels of
          []           -> []
          outer : more -> reverse (take maxCases (outer ++ concat more))
    if null cases then return (goal, info) else do
      let ds    = map fst cases
          goal' = goal { typ = Just e { lets = ctx ++ ds } }
      return (goal', info
        { giContext = ctx ++ ds
        , giCases   = Map.fromList [ (name d, ci) | (d, ci) <- cases ]
        , giLocals  = Map.union (Map.fromList [ (name d, sigOf d) | d <- ds ]) (giLocals info) })
  _ -> return (goal, info)

-- | The signature of a lemma: one explicit parameter per binder of its type.
sigOf :: CDecl -> Sig
sigOf d = [ Param (maybe 0 (length . params) (typ p)) NotHidden
          | p <- maybe [] params (typ d) ]

-- | The case analyses of a problem and, up to the given depth, those of
--   the goals of their minor premises: one list per depth.
generate :: Map String (String, RecInfo, [CDecl]) -> (CExpr -> CExpr) -> Int -> Problem
         -> TCM [[(CDecl, CaseInfo)]]
generate byData unfold depth0 pr0 = go depth0 [pr0]
  where
    go 0 _   = return []
    go _ []  = return []
    go depth prs = do
      found <- concat <$> mapM (\ pr -> catMaybesM (map (analysis byData unfold pr) (prVars pr))) prs
      nested <- go (depth - 1) (concat [ subs | (_, _, subs) <- found ])
      return ([ (d, ci) | (d, ci, _) <- found ] : nested)
    catMaybesM ms = foldr (\ m acc -> m >>= \ r -> maybe acc (\ x -> (x :) <$> acc) r) (return []) ms

-- | The case analysis of a problem on a variable, and the problems of its
--   minor premises.
analysis :: Map String (String, RecInfo, [CDecl]) -> (CExpr -> CExpr) -> Problem -> CDecl
         -> TCM (Maybe (CDecl, CaseInfo, [Problem]))
analysis byData unfold pr x = case unfold <$> typ x of
  Just (CExpr [] _ (CSpine dn as))
    | Just (rn, ri, ctors) <- Map.lookup dn byData
    , let np = riPars ri
    , length as == np + riIdx ri
    , let (pars, idxE) = splitAt np as
    , Just idx <- mapM varOf idxE
    , length (nub idx) == length idx
    , all (`elem` map name (prVars pr)) idx
    , name x `notElem` idx
    , not (any (`Set.member` Set.unions (map exprNames pars)) (name x : idx)) -> do
        let others = [ v | v <- prVars pr, name v `notElem` (name x : idx) ]
            -- The variables that depend on the eliminated ones, in order.
            deps = reverse . snd $ foldl
              (\ (dset, acc) v ->
                 if any (`Set.member` dset) (Set.toList (maybe Set.empty exprNames (typ v)))
                   then (Set.insert (name v) dset, v : acc) else (dset, acc))
              (Set.fromList (name x : idx), []) others
            rest = [ v | v <- others, name v `notElem` map name deps ]
        branches <- forM ctors (branch pr pars idx x deps)
        case sequence branches of
          Nothing -> return Nothing
          Just bs -> do
            cn <- freshString "case"
            let minorDs = bs
                caseT   = CExpr (prLead pr ++ minorDs ++ prGPars pr) [] (prGoal pr)
            motive <- motiveOf pr idx x deps
            idxRefs <- mapM varRef [ v | i <- idx, v <- prVars pr, name v == i ]
            xRef    <- varRef x
            depRefs <- mapM varRef deps
            let ci = CaseInfo
                  { ciLead     = map name (prLead pr)
                  , ciRec      = rn
                  , ciPars     = simpleExpr "_" : pars
                  , ciMotive   = motive
                  , ciIdx      = idxRefs
                  , ciMajor    = xRef
                  , ciDeps     = depRefs
                  , ciBranches = [ (brFields b, length (brIhs b)) | b <- riBranches ri ]
                  , ciGoalPars = length (prGPars pr) }
                -- The goal of a minor premise: its binders come after the
                -- binders around it, and the variables that were not
                -- generalised stay.
                sub (CDecl _ (Just (CExpr bds _ g)) _) =
                  Problem (prLead pr ++ bds) (rest ++ bds) [] g
                sub _ = Problem [] [] [] (prGoal pr)
            return (Just (CDecl cn (Just caseT) [], ci, map sub bs))
  _ -> return Nothing
  where
    varOf (CExpr [] _ (CSpine v [])) = Just v
    varOf _                          = Nothing

-- | η-long reference to a variable.
varRef :: CDecl -> TCM CExpr
varRef d = etaVar (name d) (maybe 0 (length . params) (typ d))

-- | Copies a telescope with fresh names, substituting in the types.
--   Returns the copy and the extended substitution.
copyTel :: Map String CExpr -> [CDecl] -> TCM ([CDecl], Map String CExpr)
copyTel sub0 ds = do
  (rev, sub) <- foldM (\ (acc, s) d -> do
                  n <- freshString (takeWhile (/= '.') (name d))
                  let t  = substExpr s <$> typ d
                      d' = CDecl n t []
                  r <- varRef d'
                  return (d' : acc, Map.insert (name d) r s))
                ([], sub0) ds
  return (reverse rev, sub)

-- | The minor premise of a constructor:
--   @(fs : Φ) (Δ_c) (gs_c) → G_c@.  'Nothing' if a type is missing.
branch :: Problem -> [CExpr] -> [String] -> CDecl -> [CDecl] -> CDecl -> TCM (Maybe CDecl)
branch pr pars idx x deps c = case typ c of
  Just (CExpr cps _ (CSpine _ cres)) | all (not . null . typ) cps -> do
    let np = length pars
        (cpars, cflds) = splitAt np cps
        sub0 = Map.fromList (zip (map name cpars) pars)
    (flds, subF) <- copyTel sub0 cflds
    fRefs <- mapM varRef flds
    let js    = map (substExpr subF) (drop np cres)
        value = CExpr [] [] (CSpine (name c) (pars ++ fRefs))
        sigma = Map.fromList ((name x, value) : zip idx js)
    (deps', s1) <- copyTel sigma deps
    (gps', s2)  <- copyTel s1 (prGPars pr)
    m <- freshString "minor"
    let g = substSpine s2 (prGoal pr)
    return (Just (CDecl m (Just (CExpr (flds ++ deps' ++ gps') [] g)) []))
  _ -> return Nothing

-- | The motive @λ is x Δ gs → G@, whose binders after @x@ are typed.
motiveOf :: Problem -> [String] -> CDecl -> [CDecl] -> TCM CExpr
motiveOf pr idx x deps = do
  is <- mapM (freshString . takeWhile (/= '.')) idx
  t  <- freshString (takeWhile (/= '.') (name x))
  let arity n = (\ v -> maybe 0 (length . params) (typ v)) <$> lookup n [ (name v, v) | v <- prVars pr ]
  isRefs <- sequence [ etaVar i (fromMaybe 0 (arity o)) | (i, o) <- zip is idx ]
  tRef   <- etaVar t 0
  let sub0 = Map.fromList ((name x, tRef) : zip idx isRefs)
  (deps', s1) <- copyTel sub0 deps
  (gps', s2)  <- copyTel s1 (prGPars pr)
  return (CExpr (map untyped is ++ [untyped t] ++ deps' ++ gps') [] (substSpine s2 (prGoal pr)))

-- | Writes the case analyses of an answer as recursors (see 'CaseInfo').
restoreCases :: GoalInfo -> CExpr -> TCM CExpr
restoreCases info e0
  | Map.null (giCases info) = return e0
  | otherwise = expr e0
  where
    expr (CExpr ps ls sp) = CExpr ps ls <$> spine sp
    spine (CSpine h as0) = do
      as <- mapM expr as0
      case Map.lookup h (giCases info) of
        Just ci
          | let nl = length (ciLead ci)
                k  = length (ciBranches ci)
          , length as == nl + k + ciGoalPars ci -> do
              let (bs, more) = splitAt nl as
                  (ms, gs)   = splitAt k more
                  s          = substExpr (Map.fromList (zip (ciLead ci) bs))
                  nd         = length (ciDeps ci)
              ms' <- forM (zip ms (ciBranches ci)) $ \ (m, (nf, nih)) -> do
                CExpr mps mls msp <- etaTo (nf + nd + ciGoalPars ci) m
                ihs <- mapM (fmap untyped . const (freshString "ih")) [1 .. nih]
                let (fs, after) = splitAt nf mps
                return (CExpr (fs ++ ihs ++ after) mls msp)
              return $ CSpine (ciRec ci)
                (map s (ciPars ci) ++ [s (ciMotive ci)] ++ ms'
                 ++ map s (ciIdx ci) ++ [s (ciMajor ci)] ++ map s (ciDeps ci) ++ gs)
        _ -> return (CSpine h as)
