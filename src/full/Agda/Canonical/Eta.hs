-- | η-expansion of the variables of a record type.
--
--   Agda identifies a variable @u : Σ A B@ with the pair
--   @(u .fst , u .snd)@ of its projections (η-equality of records), and
--   its unifier uses it: in @×-≡ refl refl = refl@, the arguments
--   @p : u .fst ≡ v .fst@ are matched on although their ends are not
--   variables.  Canonical only knows the computation rules of the
--   projections: a solution that eliminates @p@ must abstract @v .fst@ in
--   a goal that does not mention it (@u ≡ v@).
--
--   So each variable @u@ of the context whose type is a record with
--   η-equality (fully applied: @R pars@) is replaced by variables for its
--   fields, @u.fst : A@ and @u.snd : B u.fst@, and by the constructor
--   applied to them in the types of the variables declared after it and
--   of the goal, where the projections of a constructor are reduced:
--   @p : u.fst ≡ v.fst@ and the goal @(u.fst , u.snd) ≡ (v.fst , v.snd)@.
--   The fields of a record type are expanded in turn.
--
--   In the answers, a field variable is written as the projection of its
--   record variable, and a constructor applied to all the projections of
--   the same variable is contracted back into it ('restoreEta').
--
--   A variable mentioned by a rewrite rule of the context (the value of a
--   @let@, a constraint) is kept: the rule could no longer apply.

module Agda.Canonical.Eta
  ( etaRecordVars
  , restoreEta
  , unfoldHead
  ) where

import Control.Monad (foldM, forM)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (isNothing)
import Data.Set qualified as Set

import Agda.Canonical.Types
import Agda.Canonical.Utils (etaVar, freshString)
import Agda.Syntax.Common (HasEta' (..), Hiding (..), Induction (..))
import Agda.Syntax.Internal (ConHead (..), unDom)
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Signature (HasConstInfo (getConstInfo))

-- | A record type whose variables are expanded.
data EtaRec = EtaRec
  { erCon   :: String
      -- ^ Its constructor.
  , erPars  :: Int
      -- ^ The number of parameters of the constructor that are those of
      --   the record.
  , erProjs :: [String]
      -- ^ Its projections, in the order of the fields.
  , erCtorT :: CExpr
      -- ^ The type of the constructor.
  }

-- | Replaces the variables of a record type with η-equality by their
--   fields, in a goal declared directly (not through a continuation).
etaRecordVars :: GoalInfo -> CDecl -> TCM (CDecl, GoalInfo)
etaRecordVars info goal = case typ goal of
  Just e | isNothing (giCont info), null (giRefold info) -> do
    let ctx   = lets e
        -- The names that the rewrite rules of the context mention.
        ruled = Set.unions [ exprNames (CExpr [] [] s)
                           | d <- ctx, CEquation l r _ <- equations d, s <- [l, r] ]
        plain d = name d `elem` giNames info && null (equations d)
               && Map.notMember (name d) (giHyps info) && name d `Set.notMember` ruled
        canon = Map.fromList [ (q, n) | (n, q) <- Map.toList (giDefs info) ]
        ctorTypes = Map.fromList [ (name d, t) | d <- ctx, Just t <- [typ d] ]
    -- The record types of the context that can be expanded.
    records <- fmap (Map.fromList . concat) $ forM (Map.toList (giDefs info)) $ \ (n, q) ->
      theDef <$> getConstInfo q >>= \case
        RecordDefn rd
          | YesEta <- _recEtaEquality rd, _recInduction rd /= Just CoInductive
          , Just c <- Map.lookup (conName (_recConHead rd)) canon
          , Just ps <- mapM ((`Map.lookup` canon) . unDom) (_recFields rd)
          , Just ct <- Map.lookup c ctorTypes
          , let np = length (params ct) - length ps, np >= 0 ->
              return [(n, EtaRec c np ps ct)]
        _ -> return []
    if Map.null records then return (goal, info) else do
      (ctx', sub, fields) <- expand records (unfoldHead ctx) plain ctx
      if null fields then return (goal, info) else do
        let red    = reduceProjs records
            goalT  = red (substExpr sub e { lets = [] })
            locals = Map.fromList [ (name d, sigOf d) | (d, _) <- fields ]
            eta    = EtaInfo
              { etaFields = Map.fromList [ (name d, v) | (d, v) <- fields ]
              , etaCons   = Map.fromList [ (erCon r, (erPars r, erProjs r)) | r <- Map.elems records ] }
            goal'  = goal { typ = Just goalT { lets = ctx' } }
        return (goal', info { giContext = ctx'
                            , giLocals  = Map.union locals (giLocals info)
                            , giEta     = eta })
  _ -> return (goal, info)

-- | Expands the plain variables of a record type, in order.  Returns the
--   new context, the substitution of the expanded variables by the
--   constructor applied to their fields, and the field variables with the
--   projections they stand for.
expand :: Map String EtaRec -> (CExpr -> CExpr) -> (CDecl -> Bool) -> [CDecl]
       -> TCM ([CDecl], Map String CExpr, [(CDecl, CExpr)])
expand records unfold plain ctx0 = do
  (rev, sub, fs) <- foldM step ([], Map.empty, []) ctx0
  return (reverse rev, sub, reverse fs)
  where
    red = reduceProjs records
    step (acc, sub, fs) d0 = go (acc, sub, fs) True d0
    -- @top@: the declaration comes from the context, not from the fields
    -- of an expanded variable (which are always expanded).
    go (acc, sub, fs) top d0 = do
      let d = d0 { typ = red . substExpr sub <$> typ d0 }
      case unfold <$> typ d of
        Just (CExpr [] _ (CSpine r as))
          | not top || plain d0
          , Just rc <- Map.lookup r records
          , length as == erPars rc -> do
              let CExpr cps _ _ = erCtorT rc
                  (pars, flds)  = splitAt (erPars rc) cps
                  sub0 = Map.fromList (zip (map name pars) as)
                  base = takeWhile (/= '.') (name d)
              -- The fields, each typed in terms of the previous ones.
              (_, newDs) <- foldM (\ (s, ds) f -> do
                  n <- freshString base
                  let t = red . substExpr s <$> typ f
                      nd = CDecl n t []
                  ref <- etaVar n (maybe 0 (length . params) t)
                  return (Map.insert (name f) ref s, ds ++ [nd]))
                (sub0, []) flds
              refs <- mapM (\ nd -> etaVar (name nd) (maybe 0 (length . params) (typ nd))) newDs
              let value = CExpr [] [] (CSpine (erCon rc) (as ++ refs))
                  proj p = CExpr [] [] (CSpine p (as ++ [simpleExpr (name d)]))
                  -- A field of an expanded variable is expanded after it:
                  -- the substitution is composed.
                  sub'   = Map.insert (name d) value
                             (Map.map (red . substExpr (Map.singleton (name d) value)) sub)
                  fs'    = reverse (zip newDs (map proj (erProjs rc))) ++ fs
              -- The fields may themselves be records.
              foldM (\ st nd -> go st False nd) (acc, sub', fs') newDs
        _ -> return (d : acc, sub, fs)

-- | Unfolds the abbreviations at the head of a type (@A × B@ is
--   @Σ A (λ _ → B)@): the definitions of the context with one rule whose
--   patterns are distinct variables.
unfoldHead :: [CDecl] -> CExpr -> CExpr
unfoldHead ctx = go (10 :: Int)
  where
    defs  = Map.fromList [ (name d, d) | d <- ctx ]
    go 0 e = e
    go n e@(CExpr [] ls (CSpine h as))
      | Just d <- Map.lookup h defs
      , [CEquation (CSpine _ pats) r True] <- equations d
      , length pats == length as
      , Just vs <- mapM patVar pats
      , length (Set.fromList vs) == length vs
      = go (n - 1) (CExpr [] ls (substSpine (Map.fromList (zip vs as)) r))
    go _ e = e
    -- A pattern variable, possibly η-expanded: @λ zs → v zs@.
    patVar (CExpr zs [] (CSpine v ws))
      | Map.notMember v defs
      , map (CExpr [] [] . (`CSpine` []) . name) zs == ws = Just v
    patVar _ = Nothing

-- | The signature of a variable: one explicit parameter per binder of its type.
sigOf :: CDecl -> Sig
sigOf d = [ Param (maybe 0 (length . params) (typ p)) NotHidden
          | p <- maybe [] params (typ d) ]

-- | Reduces the projections of a constructor of the expanded records:
--   @p pars (c pars' as) rest@ is the field @a@ applied to @rest@.
reduceProjs :: Map String EtaRec -> CExpr -> CExpr
reduceProjs records = expr
  where
    projs = Map.fromList [ (p, (erPars r, erCon r, i))
                         | r <- Map.elems records, (i, p) <- zip [0 ..] (erProjs r) ]
    expr (CExpr ps ls sp) = CExpr (map decl ps) (map decl ls) (spine sp)
    decl d = d { typ = expr <$> typ d }
    spine (CSpine h as0) =
      let as = map expr as0 in
      case Map.lookup h projs of
        Just (np, c, i)
          | CExpr [] _ (CSpine c' cas) : rest <- drop np as, c' == c
          , i < length cas - np ->
              spine (applyTo (cas !! (np + i)) rest)
        _ -> CSpine h as

-- | An expression applied to arguments, β-reduced once.
applyTo :: CExpr -> [CExpr] -> CSpine
applyTo f as = substSpine (Map.singleton hole f) (CSpine hole as)
  where hole = "η.hole"

-- | Writes the field variables of an answer as projections of their
--   record variables, and contracts a constructor applied to all the
--   projections of the same expression.
restoreEta :: EtaInfo -> CExpr -> CExpr
restoreEta eta e0
  | Map.null (etaFields eta) = e0
  | otherwise = contract (fixpoint (length (etaFields eta) + 1) e0)
  where
    fields = etaFields eta
    -- A field of a field is written in terms of the first field, itself a
    -- projection: the substitution is iterated.
    fixpoint :: Int -> CExpr -> CExpr
    fixpoint 0 e = e
    fixpoint n e
      | any (`Map.member` fields) (exprNames e) = fixpoint (n - 1) (substExpr fields e)
      | otherwise = e
    contract (CExpr ps ls sp) = CExpr (map decl ps) (map decl ls) (spine sp)
    decl d = d { typ = contract <$> typ d }
    spine (CSpine h as0) =
      let as = map contract as0 in
      case Map.lookup h (etaCons eta) of
        Just (np, prs)
          | length as == np + length prs
          , Just (r : rs) <- mapM projected (zip prs (drop np as))
          , all (== r) rs, CExpr [] [] sp' <- r -> sp'
        _ -> CSpine h as
    -- @p pars r@, for the projection @p@: @r@.
    projected (p, CExpr [] _ (CSpine p' bs)) | p == p', not (null bs) = Just (last bs)
    projected _ = Nothing
