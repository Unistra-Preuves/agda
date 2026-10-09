-- | Generation of recursion principles for datatypes.
--
--   Canonical does not know Agda's pattern matching, so for each datatype
--   @D@ we declare a recursor @D.rec@ with its computation rules.  For
--   @D : (pars : Δ) → (idx : Ξ) → Set@ with constructors @c : (fs : Φ) → D pars is@:
--
--   > D.rec : {l : Level} {pars : Δ}
--   >         (motive : (idx : Ξ) → D pars idx → Type l)
--   >         (minor_c : (fs : Φ) (ih : …) → motive is (c pars fs)) …
--   >         {idx : Ξ} (major : D pars idx) → motive idx major
--   >
--   > D.rec l pars motive minors _ (c _ fs) ⤇ minor_c fs (λ xs. D.rec … (f xs)) …
--
--   with one induction hypothesis @ih@ for each recursive field @f@
--   (possibly under binders @xs@).
--   "Agda.Canonical.FromCanonical" relies on this layout to print
--   applications of recursors as pattern-matching lambdas.

module Agda.Canonical.Recursor
  ( mkRecursor
  , withoutIHs
  ) where

import Data.List (isSuffixOf)
import Data.Map (Map)
import Data.Map qualified as Map

import Agda.Canonical.Types
import Agda.Canonical.Utils (etaVar, freshString)
import Agda.Syntax.Common (Hiding(..))
import Agda.TypeChecking.Monad.Base (TCM)

-- * Renaming

-- | Renaming of free variables, applied to the head of spines.
type Ren = Map String String

renE :: Ren -> CExpr -> CExpr
renE r (CExpr ps ls sp) = CExpr (map (renD r) ps) (map (renD r) ls) (renS r sp)

renD :: Ren -> CDecl -> CDecl
renD r d = d { typ = renE r <$> typ d }

renS :: Ren -> CSpine -> CSpine
renS r (CSpine h as) = CSpine (Map.findWithDefault h h r) (map (renE r) as)

-- | The name without the suffix added by 'freshString'.
baseName :: String -> String
baseName s = case takeWhile (/= '.') s of
  "" -> "x"
  b  -> b

-- | Copies a telescope with fresh names; each type is renamed according
--   to the previous binders.  Returns the extended renaming.
freshTel :: Ren -> [CDecl] -> TCM ([CDecl], Ren)
freshTel r [] = return ([], r)
freshTel r (d : ds) = do
  n' <- freshString (baseName (name d))
  let d' = (renD r d) { name = n' }
  (ds', r') <- freshTel (Map.insert (name d) n' r) ds
  return (d' : ds', r')

-- * Binders

-- | Number of binders of the type of a declaration.
declArity :: CDecl -> Int
declArity d = maybe 0 (length . params) (typ d)

-- | η-long reference to a declared variable.
varE :: CDecl -> TCM CExpr
varE d = etaVar (name d) (declArity d)

-- | A fresh wildcard with the arity of the declaration, so that the left-hand
--   sides of the computation rules stay linear.
wild :: CDecl -> TCM CExpr
wild d = do
  w <- freshString "w"
  etaVar w (declArity d)

-- * Recursor

-- | The minor premise of a constructor.
data MinorInfo = MinorInfo
  { miCtor   :: String
      -- ^ Name of the constructor.
  , miDecl   :: CDecl
      -- ^ Declaration of the minor premise.
  , miFields :: [CExpr]
      -- ^ η-long references to the fields.
  , miRecs   :: [([CDecl], [CExpr], CExpr)]
      -- ^ For each recursive field @f@: its binders @xs@, the indices of
      --   @f xs@, and @f xs@ itself.
  }

-- | Minor premise of a constructor, or 'Nothing' if its type is missing.
mkMinor
  :: Int       -- ^ Number of parameters of the datatype.
  -> String    -- ^ Name of the datatype.
  -> String    -- ^ Name of the motive.
  -> [CExpr]   -- ^ References to the parameters of the recursor.
  -> [CDecl]   -- ^ Parameters of the recursor.
  -> CDecl     -- ^ The constructor, as declared to Canonical.
  -> TCM (Maybe MinorInfo)
mkMinor np dn mN parRefs pars (CDecl cn (Just (CExpr cps _ (CSpine _ cres))) _) = do
  let r0 = Map.fromList (zip (map name (take np cps)) (map name pars))
  (flds, r1) <- freshTel r0 (drop np cps)
  fRefs <- mapM varE flds
  recs  <- concat <$> mapM recField flds
  ihDs  <- mapM (\ (xs, idxs, fApp) -> do
                   n <- freshString "ih"
                   return (typed n (CExpr xs [] (CSpine mN (idxs ++ [fApp]))))) recs
  mn <- freshString "minor"
  let resIdx  = map (renE r1) (drop np cres)
      ctorApp = CExpr [] [] (CSpine cn (parRefs ++ fRefs))
      minorT  = CExpr (flds ++ ihDs) [] (CSpine mN (resIdx ++ [ctorApp]))
  return (Just (MinorInfo cn (typed mn minorT) fRefs recs))
  where
    -- A field is recursive when its type ends in the datatype itself.
    recField f = case typ f of
      Just (CExpr xs _ (CSpine h fargs)) | h == dn -> do
        (xs', r2) <- freshTel Map.empty xs
        xRefs <- mapM varE xs'
        let idxs = map (renE r2) (drop np fargs)
            fApp = CExpr [] [] (CSpine (name f) xRefs)
        return [(xs', idxs, fApp)]
      _ -> return []
mkMinor _ _ _ _ _ _ = return Nothing

-- | The recursor of a datatype and its signature, or 'Nothing' if some
--   type is missing.
mkRecursor
  :: Int       -- ^ Number of parameters of the datatype.
  -> CDecl     -- ^ The datatype, as declared to Canonical.
  -> [CDecl]   -- ^ Its constructors, as declared to Canonical.
  -> TCM (Maybe (CDecl, Sig))
mkRecursor np (CDecl dn (Just (CExpr dps _ _)) _) ctors = do
  let rn = dn ++ ".rec"
  lN <- freshString "l"
  mN <- freshString "motive"
  tN <- freshString "t"
  (pars, rP) <- freshTel Map.empty (take np dps)
  (mIdx, _)  <- freshTel rP (drop np dps)     -- indices bound by the motive
  (idxR, _)  <- freshTel rP (drop np dps)     -- indices of the recursor
  parRefs  <- mapM varE pars
  mIdxRefs <- mapM varE mIdx
  idxRefs  <- mapM varE idxR
  let lD     = typed lN (simpleExpr "Level")
      lRef   = simpleExpr lN
      motive = typed mN (CExpr (mIdx ++ [typed tN (CExpr [] [] (CSpine dn (parRefs ++ mIdxRefs)))])
                               [] (CSpine "Type" [lRef]))
  mis <- mapM (mkMinor np dn mN parRefs pars) ctors
  case sequence mis of
    Nothing    -> return Nothing
    Just infos -> do
      majN <- freshString "major"
      let minorDs = map miDecl infos
          majD    = typed majN (CExpr [] [] (CSpine dn (parRefs ++ idxRefs)))
      motiveV   <- varE motive
      minorRefs <- mapM varE minorDs
      majRef    <- varE majD
      let common = [lRef] ++ parRefs ++ [motiveV] ++ minorRefs
          recTy  = CExpr ([lD] ++ pars ++ [motive] ++ minorDs ++ idxR ++ [majD]) []
                         (CSpine mN (idxRefs ++ [majRef]))
      eqs <- mapM (\ i -> do
                cpW  <- mapM wild pars
                idxW <- mapM wild idxR
                let pat = CExpr [] [] (CSpine (miCtor i) (cpW ++ miFields i))
                    l   = CSpine rn (common ++ idxW ++ [pat])
                    ihs = [ CExpr xs [] (CSpine rn (common ++ ix ++ [fa]))
                          | (xs, ix, fa) <- miRecs i ]
                    r   = CSpine (name (miDecl i)) (miFields i ++ ihs)
                return (CEquation l r True)) infos
      let hid  = Param `flip` Hidden
          expl = Param `flip` NotHidden
          sig  = [hid (declArity lD)] ++ map (hid . declArity) pars
              ++ [expl (declArity motive)] ++ map (expl . declArity) minorDs
              ++ map (hid . declArity) idxR ++ [expl (declArity majD)]
      return (Just (CDecl rn (Just recTy) eqs, sig))
mkRecursor _ _ _ = return Nothing

-- * Without induction hypotheses

-- | A recursor without its induction hypotheses: a case analysis.  Its
--   applications are printed as pattern-matching lambdas, which are not
--   recursive, so this is the recursor whose solutions can always be
--   written (see 'Agda.Canonical.FromCanonical.usesNestedIH').  Other
--   declarations are unchanged.
--
--   In the computation rule of a constructor, the fields are the arguments
--   of the minor premise that are also arguments of the constructor
--   (the parameters are wildcards); the induction hypotheses come after
--   them, as the last binders of the type of the minor premise.
withoutIHs :: CDecl -> CDecl
withoutIHs d@(CDecl rn (Just (CExpr ps ls sp)) eqs)
  | ".rec" `isSuffixOf` rn = CDecl rn (Just (CExpr (map dropMinor ps) ls sp)) (map dropEq eqs)
  | otherwise              = d
  where
    -- The number of induction hypotheses of each minor premise.
    ihCounts = Map.fromList
      [ (m, length ras - nf)
      | CEquation (CSpine _ las) (CSpine m ras) _ <- eqs
      , CExpr _ _ (CSpine _ cas) : _ <- [reverse las]
      , let heads = [ h | CExpr _ _ (CSpine h _) <- cas ]
            nf    = length (takeWhile (\ case CExpr _ _ (CSpine h _) -> h `elem` heads) ras) ]
    dropMinor p = case (Map.lookup (name p) ihCounts, typ p) of
      (Just k, Just (CExpr bs bls bsp)) | k > 0 ->
        p { typ = Just (CExpr (take (length bs - k) bs) bls bsp) }
      _ -> p
    dropEq (CEquation l (CSpine m ras) red) = case Map.lookup m ihCounts of
      Just k | k > 0 -> CEquation l (CSpine m (take (length ras - k) ras)) red
      _              -> CEquation l (CSpine m ras) red
withoutIHs d = d
