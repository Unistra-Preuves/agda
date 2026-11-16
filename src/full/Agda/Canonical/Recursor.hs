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
--
--   A path constructor of a higher inductive type, @p : (fs : Φ) → x ≡ y@,
--   is declared as @p : (fs : Φ) (i : I) → D pars@ with its boundary
--   @p fs i0 ⤇ x@ and @p fs i1 ⤇ y@.  Its minor premise must respect this
--   boundary, as the clauses of a function defined by pattern matching:
--
--   > minor_p fs i0 ihs = rec x        minor_p fs i1 ihs = rec y
--
--   where @rec@ of a constructor is its minor premise and @rec@ of a
--   recursive field is its induction hypothesis ('boundary').  These are
--   constraints on the parameter @minor_p@; as constraints cannot bind
--   variables, both sides are closed under 'boundaryName':
--
--   > Boundary (λ fs ihs. minor_p fs i0 ihs) = Boundary (λ fs ihs. rec x)
--   "Agda.Canonical.FromCanonical" relies on this layout to print
--   applications of recursors as pattern-matching lambdas.

module Agda.Canonical.Recursor
  ( mkRecursor
  , boundaryName
  , withoutIHs
  ) where

import Data.List (elemIndex, isSuffixOf)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (mapMaybe)

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
  , miFlds   :: [CDecl]
      -- ^ The fields, as bound by the minor premise.
  , miIHs    :: [CDecl]
      -- ^ The induction hypotheses, as bound by the minor premise, in the
      --   order of 'miRecs'.
  , miIHRefs :: [CExpr]
      -- ^ η-long references to the induction hypotheses.
  , miEnds   :: [([String], CSpine)]
      -- ^ The boundary of a path constructor: for each equation
      --   @c pars as ⤇ r@ of the constructor, the heads of @as@ (a field
      --   of the constructor, or @i0@ or @i1@) and @r@, where the fields
      --   are those of 'miFlds'.
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
mkMinor np dn mN parRefs pars (CDecl cn (Just (CExpr cps _ (CSpine _ cres))) ceqs) = do
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
      ren n   = Map.findWithDefault n n r1
      ends    = [ (map ren hs, renS r1 r)
                | CEquation (CSpine _ las) r _ <- ceqs
                , let hs = [ h | CExpr _ _ (CSpine h _) <- drop np las ] ]
  ihRefs <- mapM varE ihDs
  return (Just (MinorInfo cn (typed mn minorT) fRefs recs flds ihDs ihRefs ends))
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

-- | The symbol under which both sides of a constraint on the boundary of
--   a minor premise are closed.  It has no type nor rule: two of its
--   applications are equal when their arguments are.
boundaryName :: String
boundaryName = "Boundary"

-- | The constraints on the minor premise of a path constructor, given the
--   number of parameters of the datatype and the minor premises of the
--   constructors declared before it:
--
--   > minor fs[i := i0] ihs = rec x
--
--   for each end @c pars fs[i := i0] ⤇ x@ of the constructor, where
--
--   > rec (c' pars as) = minor_c' as (λ ys. rec (a ys)) …
--   > rec (f as)       = ih_f as                -- f a recursive field
--
--   An end that is neither (e.g. an @hcomp@) gives no constraint.
boundary :: Int -> [MinorInfo] -> MinorInfo -> [CEquation]
boundary np before i = mapMaybe end (miEnds i)
  where
    fnames = map name (miFlds i)
    ihOf   = Map.fromList [ (h, name d) | ((_, _, CExpr _ _ (CSpine h _)), d) <- zip (miRecs i) (miIHs i) ]
    minors = Map.fromList [ (miCtor m, m) | m <- before ]

    end (hs, r)
      | length hs /= length fnames = Nothing
      | otherwise = do
          r' <- recS r
          let fixed  = Map.fromList [ (f, simpleExpr h) | (f, h) <- zip fnames hs, f /= h ]
              bs     = [ untyped f | f <- fnames, f `Map.notMember` fixed ] ++ map (untyped . name) (miIHs i)
              l      = CSpine (name (miDecl i)) (map (substExpr fixed) (miFields i ++ miIHRefs i))
              close sp | null bs   = sp
                       | otherwise = CSpine boundaryName [CExpr bs [] sp]
          return (CEquation (close l) (close r') True)

    recS (CSpine h as)
      | Just m <- Map.lookup h minors = do
          let fas = drop np as
              pos (_, _, CExpr _ _ (CSpine f _)) = elemIndex f (map name (miFlds m))
          ihs <- mapM (\ rc -> do
                         k <- pos rc
                         CExpr ys _ body <- if k < length fas then Just (fas !! k) else Nothing
                         CExpr ys [] <$> recS body) (miRecs m)
          if length fas == length (miFlds m)
            then Just (CSpine (name (miDecl m)) (fas ++ ihs)) else Nothing
      | Just ih <- Map.lookup h ihOf  = Just (CSpine ih as)
      | otherwise                     = Nothing

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
    Just infos0 -> do
      majN <- freshString "major"
      -- Each minor premise with its boundary, in terms of the previous ones.
      let infos   = [ i { miDecl = (miDecl i) { equations = boundary np (take k infos0) i } }
                    | (k, i) <- zip [0 ..] infos0 ]
          minorDs = map miDecl infos
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
      let hid n  = Param n Hidden
          expl n = Param n NotHidden
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
--
--   In the constraints on the boundary of a minor premise ('boundary'),
--   the induction hypotheses are no longer bound nor given to the minor
--   premises; a constraint that states that an end is an induction
--   hypothesis is dropped.
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
    -- The induction hypotheses: the last binders of the minor premises.
    ihNames = concat
      [ map name (drop (length bs - k) bs)
      | p <- ps, Just k <- [Map.lookup (name p) ihCounts], Just (CExpr bs _ _) <- [typ p] ]
    dropMinor p0 = case (Map.lookup (name p) ihCounts, typ p) of
      (Just k, Just (CExpr bs bls bsp)) | k > 0 ->
        p { typ = Just (CExpr (take (length bs - k) bs) bls bsp) }
      _ -> p
      where p = p0 { equations = mapMaybe dropEnd (equations p0) }
    dropEnd (CEquation l r red)
      | usesIH l' || usesIH r' = Nothing
      | otherwise              = Just (CEquation l' r' red)
      where l' = dropS l
            r' = dropS r
    dropS (CSpine h as) = CSpine h (take (length as - Map.findWithDefault 0 h ihCounts) (map dropE as))
    dropE (CExpr bs bls sp) = CExpr (filter ((`notElem` ihNames) . name) bs) bls (dropS sp)
    usesIH (CSpine h as) = h `elem` ihNames || any (\ (CExpr _ _ sp) -> usesIH sp) as
    dropEq (CEquation l (CSpine m ras) red) = case Map.lookup m ihCounts of
      Just k | k > 0 -> CEquation l (CSpine m (take (length ras - k) ras)) red
      _              -> CEquation l (CSpine m ras) red
withoutIHs d = d
