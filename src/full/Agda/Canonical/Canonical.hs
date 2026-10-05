
module Agda.Canonical.Canonical where

import Control.Monad (foldM, forM, replicateM, zipWithM)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.Foldable (foldlM)
import Data.IntMap qualified as IntMap
import Data.Map (Map, insert, member)
import Data.Map qualified as Map

import Agda.Canonical.FFI (runCanonical)
import Agda.Canonical.FromCanonical (cexprToAgda)
import Agda.Canonical.Types
import Agda.Interaction.Base (Rewrite)
import Agda.Interaction.BasicOps (parseExprIn)
import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Builtin
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty qualified as P
import Agda.Syntax.Internal
import Agda.Syntax.Position (Range)
import Agda.TypeChecking.Level (reallyUnLevelView)
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Context (getContextArgs, getContextTelescope, underAbstraction)
import Agda.TypeChecking.Monad.MetaVars
import Agda.TypeChecking.Monad.Signature (HasConstInfo (getConstInfo))
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope (teleNames, telView)
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Maybe (fromMaybe)
import Agda.Utils.Size (size)

{- General information.

  All converting functions returning types are TCM (C_, [CDecl], Map String Bool).

  For now the monad is for the sake of readability / compatibility.
  The first object is the actual object created by the function.

  The second object is the context we are creating for Canonical.
  In this context, we have to put all the datatypes, function definitions
  and constructors we want Canonical to be able to use.
  Since we are building this context on the fly while recursively converting a term,
  we have to keep track of it throughout the conversion.

  The final object is to keep track of already encountered datatypes / constructors
  and avoid infinite recursion / putting them multiple times in the context.

-}




freshString :: MonadFresh NameId m => String -> m String
freshString s = do
  NameId n _ <- fresh
  return (s ++ "." ++ show n)

{-
  Converts a qualified name of Agda into a string.
-}
nameToString :: QName -> String
nameToString = P.prettyShow <$> qnameName

arityOf :: Term -> Int
arityOf (Pi _ b) = 1 + arityOf (unEl (unAbs b))
arityOf _        = 0

appliedTerms :: [Elim' Term] -> [Term]
appliedTerms es = [unArg t | Apply t <- es]

-- | Types fonctionnels successifs avant chaque argument (instanciés).
fnTypes :: Type -> [Term] -> [Type]
fnTypes t (a : as)
  | Pi _ b <- unEl t = t : fnTypes (absApp b a) as
fnTypes _ _ = []

-- | Épluche des Pi en liant leurs variables aux noms des paramètres du λ.
stripPi :: [String] -> [String] -> Term -> Maybe ([String], Term)
stripPi [] ns t = Just (ns, t)
stripPi (p : ps) ns (Pi _ b) = case b of
  Abs _ _   -> stripPi ps (p : ns) (unEl (unAbs b))
  NoAbs _ _ -> stripPi ps ns (unEl (unAbs b))
stripPi _ _ _ = Nothing

-- Déclarations de Pi / Pi.mk / Pi.f


-- | Ajoute j paramètres à un CExpr et les applique à sa tête.
etaExtend :: Int -> CExpr -> TCM CExpr
etaExtend j (CExpr ps ls (CSpine h args)) = do
  xs <- replicateM j (freshString "x")
  return $ CExpr (ps ++ map (\x -> CDecl x Nothing []) xs) ls
                 (CSpine h (args ++ map simpleExpr xs))

-- | Variable x d'arité k, η-longue : λz. x z.
etaVar :: String -> Int -> TCM CExpr
etaVar x k = do
  zs <- replicateM k (freshString "z")
  return $ CExpr (map (\z -> CDecl z Nothing []) zs) [] (CSpine x (map simpleExpr zs))

appendArg :: CSpine -> CExpr -> CSpine
appendArg (CSpine h args) ce = CSpine h (args ++ [ce])


-- | Un paramètre : arité de son type, et visibilité.


isExplicit :: Param -> Bool
isExplicit = (== NotHidden) . pHiding

-- symSig  : alignée sur les elims Agda (constructeurs : sans paramètres du datatype)
-- symDecl : telle que déclarée à Canonical (c'est elle qu'on garde en trace)
data Sym = Sym { symSig :: Sig, symTy :: Maybe Type, symDecl :: Sig }

localSym :: Sig -> Sym
localSym s = Sym s Nothing s

-- | Signature syntaxique (variables liées).
termSig :: Term -> Sig
termSig (Pi a b) = Param (arityOf (unEl (unDom a))) (getHiding a) : termSig (unEl (unAbs b))
termSig _        = []

-- | Signature d'un type clos, avec dépliage des alias (telView).
tySig :: Type -> TCM Sig
tySig t = do
  TelV tel _ <- telView t
  go tel
  where
    go :: Telescope -> TCM Sig
    go EmptyTel = return []
    go (ExtendTel dom b) = do
      TelV d _ <- telView (unDom dom)
      rest <- underAbstraction dom b go
      return (Param (size d) (getHiding dom) : rest)

globalSym :: QName -> TCM Sym
globalSym q = do
  def <- getConstInfo q
  sg  <- tySig (defType def)
  return $ case theDef def of
    ConstructorDefn cd -> Sym (drop (_conPars cd) sg) Nothing sg
    _                  -> Sym sg (Just (defType def)) sg

-- Pi / Pi.mk / Pi.f, dépendant des niveaux

piSigs :: [(String, Sig)]
piSigs = [("Pi", base), ("Pi.mk", base ++ [p 1]), ("Pi.f", base ++ [p 0, p 0])]
  where p n  = Param n NotHidden
        base = [p 0, p 0, p 0, p 1]

-- | Déclare Pi (et Level, _⊔_ dont il dépend) si ce n'est pas déjà fait.
withPi :: [CDecl] -> Seen -> TCM ([CDecl], Seen)
withPi lets ald
  | "Pi" `member` ald = return (lets, ald)
  | otherwise = do
      lq <- fromMaybe __IMPOSSIBLE__ <$> getName' BuiltinLevel
      mq <- fromMaybe __IMPOSSIBLE__ <$> getName' PrimLevelMax
      let ald0 = foldr (uncurry insert) ald piSigs
      (lets1, ald1) <- foldlM (\(l, a) q -> gatherDatatypeInformations q [] l a)
                              (lets, ald0) [lq, mq]
      return (piDecls ++ lets1, ald1)

-- | Arguments d'un Pi : les deux niveaux, le domaine, la famille.
data PiP = PiP { ppLu, ppLv, ppA, ppB :: CExpr }

piArgs :: PiP -> [CExpr]
piArgs (PiP u v a b) = [u, v, a, b]

sortLevel :: Sort -> TCM Term
sortLevel (Type l) = reallyUnLevelView l
sortLevel (SSet l) = reallyUnLevelView l
sortLevel _        = return (Level (Max 0 []))

piParts :: Dom Type -> Abs Type -> [String] -> [CDecl] -> Seen -> Map String Sig
        -> TCM (PiP, [CDecl], Seen)
piParts a b names lets ald art = do
  (nm, names') <- case b of
    NoAbs _ _ -> (\n -> (n, names))        <$> freshString "a"
    Abs n _   -> (\n' -> (n', n' : names)) <$> freshString n
  lu <- sortLevel (getSort (unDom a))
  lv <- sortLevel (getSort (unAbs b))
  (eu, l1, a1) <- toCExpr lu names  [] lets ald False False art
  (ev, l2, a2) <- toCExpr lv names' [] l1   a1  False False art
  (ea, l3, a3) <- toCExpr (unEl $ unDom a) names [] l2 a2 False False art
  let art' = Map.insert nm (termSig (unEl $ unDom a)) art
  (eb, l4, a4) <- toCExpr (unEl $ unAbs b) names' [CDecl nm Nothing []] l3 a3 False False art'
  (l5, a5) <- withPi l4 a4
  return (PiP eu ev ea eb, l5, a5)

fixArg :: [String] -> Int -> Maybe Term -> CExpr -> [CDecl] -> Seen -> Map String Sig
       -> TCM (CExpr, [CDecl], Seen)
fixArg names k mty ce@(CExpr ps ls sp) lets ald art
  | m == k = return (ce, lets, ald)
  | m < k  = do
      ce' <- etaExtend (k - m) ce
      return (ce', lets, ald)
  | otherwise =
      case mty >>= stripPi (map name outer) names of
        Just (names', Pi dom b) -> do
          (pp, lets1, ald1) <- piParts dom b names' lets ald art
          (inner', lets2, ald2) <- fixArg names' 1 (Just (Pi dom b)) (CExpr inner [] sp) lets1 ald1 art
          return (CExpr outer ls (CSpine "Pi.mk" (piArgs pp ++ [inner'])), lets2, ald2)
        _ -> return (ce, lets, ald)
  where
    m = length ps
    (outer, inner) = splitAt k ps

applyHead :: String -> Maybe Sym -> [Term] -> [CExpr] -> [String] -> [CDecl]
          -> Seen -> Map String Sig
          -> TCM (CSpine, [CDecl], [CDecl], Seen)
applyHead hd Nothing _ cargs _ lets ald _ =
  return (CSpine hd cargs, [], lets, ald)
applyHead hd (Just Sym { symSig = sg, symTy = mty }) terms cargs names lets0 ald0 art = do
  let ar   = length sg
      n    = length cargs
      ftys = maybe [] (`fnTypes` terms) mty
      expTy i = case drop i ftys of
        (t : _) | Pi dom _ <- unEl t -> Just (unEl (unDom dom))
        _                            -> Nothing
      fixStep (acc, ls, al) (i, k, ce) = do
        (ce', ls', al') <- fixArg names k (expTy i) ce ls al art
        return (acc ++ [ce'], ls', al')
      exStep (g, ls, al) (i, ce) =
        case drop i ftys of
          (t : _) | Pi dom b <- unEl t -> do
            let dty = unEl (unDom dom)
            (pp, ls1, al1)  <- piParts dom b names ls al art
            (ce', ls2, al2) <- fixArg names (arityOf dty) (Just dty) ce ls1 al1 art
            return (CSpine "Pi.f" (piArgs pp ++ [CExpr [] [] g, ce']), ls2, al2)
          _ -> return (appendArg g ce, ls, al)
  (fixed, lets1, ald1) <- foldM fixStep ([], lets0, ald0) (zip3 [0 ..] (map pArity sg) cargs)
  xs   <- replicateM (max 0 (ar - n)) (freshString "x")
  etas <- zipWithM etaVar xs (map pArity (drop n sg))
  (sp, lets2, ald2) <- foldM exStep (CSpine hd (fixed ++ etas), lets1, ald1)
                                    (zip [ar ..] (drop ar cargs))
  return (sp, map (\x -> CDecl x Nothing []) xs, lets2, ald2)

{-
  This function converts an Agda term into a Canonical declaration.
-}

toCDecl :: Term -> -- ^ The term to convert
           String -> -- ^ The name of the declaration
           [CEquation] -> -- ^ The constraints / definitions
           [String] -> -- ^ already bound names
           [CDecl] -> -- ^ let declarations
           Seen ->
           -- Map String Bool -> -- ^ already seen definitions² / constructors
           Bool -> -- ^ is at top level
           Map String Sig -> -- ^ arities
           TCM (CDecl, [CDecl], Seen, Map String Sig)
toCDecl t name eqs bindnames lets ald tplvl art = do
  (typ, lets, ald) <- toCExpr t bindnames [] lets ald tplvl True art
  return (CDecl { name, typ = Just typ, equations = eqs }, lets, ald, insert name (termSig t) art)
{-
  This function converts an Agda term into a Canonical expression.
-}

toCExpr :: Term -> -- ^ The term to convert
           [String] -> -- ^ Bound names
           [CDecl] -> -- ^ Pi declarations
           [CDecl] -> -- ^ Context
           Seen -> -- ^ already seen constructors / definitions
           Bool -> -- ^ is at top level
           Bool -> -- ^ to type ?
           Map String Sig -> -- ^ Arities
           TCM (CExpr, [CDecl], Seen)
toCExpr t bindnames pidecl letdecl ald tplvl totyp art =
  case t of
    Pi a b | totyp -> do
      (newnames, na) <- case b of
        NoAbs _ _ -> do n' <- freshString "a"; return (bindnames, n')
        Abs n _   -> do n' <- freshString n;   return (n' : bindnames, n')
      (domdecl, lets, ald', art') <- toCDecl (unEl $ unDom a) na [] bindnames letdecl ald False art
      toCExpr (unEl $ unAbs b) newnames (domdecl : pidecl) lets ald' tplvl totyp art'
    Pi a b -> do
      (pp, lets, ald') <- piParts a b bindnames letdecl ald art
      return ( CExpr (reverse pidecl) (if tplvl then reverse lets else []) (CSpine "Pi" (piArgs pp))
             , lets, ald' )
    Lam a b -> do          -- inchangé
      let (newnames, name) = case b of
                      NoAbs _ _ -> (bindnames, "_")
                      Abs n _ -> (n : bindnames, n)
      toCExpr (unAbs b) newnames (CDecl name Nothing [] : pidecl) letdecl ald tplvl False art
      -- return (e, d, a, 0)
    _ -> do
      (spine, extra, lets, ald) <- toCSpine t bindnames letdecl ald art
      return ( CExpr { params = reverse pidecl ++ extra
                     , lets   = if tplvl then reverse lets else []
                     , spine }
             , lets, ald)

toCSpine :: Term -> [String] -> [CDecl] -> Seen -> Map String Sig
         -> TCM (CSpine, [CDecl], [CDecl], Seen)
toCSpine t bindnames lets ald art =
  case t of
    Var i el -> do
      (args, lets, ald) <- elimsToCExpr el bindnames lets ald art
      let h = bindnames !! i
      applyHead h (localSym <$> Map.lookup h art) (appliedTerms el) args bindnames lets ald art
      -- applyHead h (flip Sym Nothing <$> Map.lookup h art) (appliedTerms el) args bindnames lets ald art
    Sort (Type l) -> do
      t' <- reallyUnLevelView l
      (arg, lets, ald) <- toCExpr t' bindnames [] lets ald False False art
      return (CSpine { head = "Type", args = [arg] }, [], lets, ald)
    Sort (SSet l) -> do
      t' <- reallyUnLevelView l
      (arg, lets, ald) <- toCExpr t' bindnames [] lets ald False False art
      return (CSpine { head = "ß", args = [arg] }, [], lets, ald)
    Sort IntervalUniv ->
      return (CSpine { head = "IUniv", args = [] }, [], lets, ald)
    Level l -> do
      t' <- reallyUnLevelView l
      toCSpine t' bindnames lets ald art
    Def qname e -> do
      (args, lets, ald) <- elimsToCExpr e bindnames lets ald art
      (lets, ald) <- gatherDatatypeInformations qname bindnames lets ald
      sym <- globalSym qname
      applyHead (P.prettyShow (qnameName qname)) (Just sym) (appliedTerms e) args bindnames lets ald art
    Con hd _ e -> do
      infos <- getConstInfo (conName hd)
      let dataname = case theDef infos of
                       ConstructorDefn cd -> _conData cd
                       _ -> __IMPOSSIBLE__
      (args, lets, ald) <- elimsToCExpr e bindnames lets ald art
      (lets, ald) <- gatherDatatypeInformations dataname bindnames lets ald
      sym <- globalSym (conName hd)
      applyHead (P.prettyShow . qnameName $ conName hd) (Just sym) (appliedTerms e) args bindnames lets ald art
    e -> return (CSpine { head = P.prettyShow e, args = [] }, [], lets, ald)

{-
  This function converts a list of Agda eliminators into Canonical expressions.
-}

elimsToCExpr :: [Elim' Term] -> -- ^ The eliminators
                [String] -> -- ^ Bound names
                [CDecl] -> -- ^ Context
                Seen -> -- Already seen datatypes / constructors
                Map String Sig -> -- ^ Arities
                TCM ([CExpr], [CDecl], Seen)
elimsToCExpr e names lets ald art =
  case e of
    [] -> return ([], lets, ald)
    el : els -> do
      -- Convert the first argument
      (el, lets, ald) <- elimToCExpr el names lets ald art
      -- Convert the rest
      (els, lets, ald) <- elimsToCExpr els names lets ald art
      return (el : els, lets, ald)
  where

  elimToCExpr :: Elim' Term -> -- The eliminator
                 [String] -> -- Bound names
                 [CDecl] -> -- Context
                 Seen -> -- Already seen datatypes / constructors
                 Map String Sig -> -- Arities
                 TCM (CExpr, [CDecl], Seen)
  elimToCExpr c names lets ald art =
    case c of
      -- If it's an application, we just convert the argument into an expression
      Apply t -> do
        toCExpr (unArg t) names [] lets ald False False art
        -- return (e,d,a)
      -- IApply _ _ _  -> __IMPOSSIBLE__
      -- Unhandled cases
      e -> return $ (
        CExpr {
          params = [],
          lets = [],
          spine = CSpine {
              head = P.prettyShow e,
              args = []
            }
        }, lets, ald)

conParCount :: QName -> TCM Int
conParCount q = do
  d <- getConstInfo q
  return $ case theDef d of
    ConstructorDefn cd -> _conPars cd
    _                  -> __IMPOSSIBLE__

-- | Complète un CExpr à k paramètres (η-longue).
etaTo :: Int -> CExpr -> TCM CExpr
etaTo k ce
  | m < k     = etaExtend (k - m) ce
  | otherwise = return ce
  where m = length (params ce)

-- | Motif Agda -> argument du membre gauche. Nothing = motif non supporté.
--   Variable -> wild card ; DotP -> wild card fraîche ;
--   constructeur -> paramètres du datatype en wild cards (absents des motifs).
patToCExpr :: [String] -> DeBruijnPattern -> TCM (Maybe CExpr)
patToCExpr names p = case p of
  VarP _ x -> return . Just $ simpleExpr (names !! dbPatVarIndex x)
  DotP _ _ -> Just . simpleExpr <$> freshString "w"
  ConP c _ ps -> do
    np   <- conParCount (conName c)
    ws   <- replicateM np (simpleExpr <$> freshString "p")
    subs <- mapM (patToCExpr names . namedArg) ps
    return $ (\ss -> CExpr [] [] (CSpine (nameToString (conName c)) (ws ++ ss)))
               <$> sequence subs
  _ -> return Nothing        -- LitP, ProjP, IApplyP, DefP

-- | Consomme jusqu'à k Lam du corps, avec des noms frais.
peel :: Int -> [String] -> Term -> TCM ([String], [String], Term)
peel k ns (Lam _ b) | k > 0 = do
  let nm = case b of { Abs n _ -> n; NoAbs n _ -> n }
  x <- freshString nm
  let ns' = case b of { Abs{} -> x : ns; NoAbs{} -> ns }
  (xs, ns'', t) <- peel (k - 1) ns' (unAbs b)
  return (x : xs, ns'', t)
peel _ ns t = return ([], ns, t)

clauseToEquation :: QName -> Sig -> Clause -> [CDecl] -> Seen
                 -> TCM (Maybe CEquation, [CDecl], Seen)
clauseToEquation qn sg cl lets ald =
  case clauseBody cl of
    Nothing   -> skip
    Just body -> do
      let tel  = clauseTel cl
          pats = map namedArg (namedClausePats cl)
          ar   = length sg
          n    = length pats
      ns <- mapM freshString (teleNames tel)
      let bindn = reverse ns                       -- Var i  ->  bindn !! i
          art0  = Map.fromList
                    [ (x, termSig (unEl (snd (unDom d)))) | (x, d) <- zip ns (telToList tel) ]
      mps <- mapM (patToCExpr bindn) pats
      case sequence mps of
        Just lhs0 | n <= ar -> do
          lhs               <- zipWithM etaTo (map pArity sg) lhs0
          (xs, bindn', b')  <- peel (ar - n) bindn body
          (e, lets', ald')  <- toCExpr b' bindn' [] lets ald False False art0
          let k = ar - n - length xs
              j = length (params e)
          if j > k then skip else do
            e' <- etaExtend (k - j) e
            let extra = map simpleExpr (xs ++ map name (params e'))
            return ( Just (CEquation (CSpine (nameToString qn) (lhs ++ extra)) (spine e') True)
                   , lets', ald' )
        _ -> skip
  where skip = return (Nothing, lets, ald)

clausesToEquations :: QName -> Sig -> [Clause] -> [CDecl] -> Seen
                   -> TCM ([CEquation], [CDecl], Seen)
clausesToEquations qn sg cls lets ald =
  foldlM (\(eqs, ls, al) cl -> do
            (me, ls', al') <- clauseToEquation qn sg cl ls al
            return (eqs ++ maybe [] pure me, ls', al'))
         ([], lets, ald) cls

-- Principes de récursion générés

type Ren = Map String String

renE :: Ren -> CExpr -> CExpr
renE r (CExpr ps ls sp) = CExpr (map (renD r) ps) (map (renD r) ls) (renS r sp)

renD :: Ren -> CDecl -> CDecl
renD r d = d { typ = renE r <$> typ d }

renS :: Ren -> CSpine -> CSpine
renS r (CSpine h as) = CSpine (Map.findWithDefault h h r) (map (renE r) as)

baseName :: String -> String
baseName s = case takeWhile (/= '.') s of { "" -> "x"; b -> b }

-- | Copie des binders avec des noms frais ; les types sont renommés au fil de l'eau.
freshTel :: Ren -> [CDecl] -> TCM ([CDecl], Ren)
freshTel r [] = return ([], r)
freshTel r (d : ds) = do
  n' <- freshString (baseName (name d))
  let d' = (renD r d) { name = n' }
  (ds', r') <- freshTel (Map.insert (name d) n' r) ds
  return (d' : ds', r')

declArity :: CDecl -> Int
declArity d = maybe 0 (length . params) (typ d)

-- | Référence η-longue à une variable déclarée.
varE :: CDecl -> TCM CExpr
varE d = etaVar (name d) (declArity d)

-- | Wild card fraîche de même arité (motif non linéaire évité).
wild :: CDecl -> TCM CExpr
wild d = do w <- freshString "w"; etaVar w (declArity d)

data MinorInfo = MinorInfo
  { miCtor   :: String
  , miDecl   :: CDecl                        -- prémisse mineure
  , miFields :: [CExpr]                      -- références aux champs
  , miRecs   :: [([CDecl], [CExpr], CExpr)]  -- champs récursifs : (binders, indices, f xs)
  }

mkMinor :: Int -> String -> String -> [CExpr] -> [CDecl] -> CDecl -> TCM (Maybe MinorInfo)
mkMinor np dn mN parRefs pars (CDecl cn (Just (CExpr cps _ (CSpine _ cres))) _) = do
  let r0 = Map.fromList (zip (map name (take np cps)) (map name pars))
  (flds, r1) <- freshTel r0 (drop np cps)
  fRefs <- mapM varE flds
  recs  <- concat <$> mapM recField flds
  ihDs  <- mapM (\(xs, idxs, fApp) -> do
                   n <- freshString "ih"
                   return (typed n (CExpr xs [] (CSpine mN (idxs ++ [fApp]))))) recs
  mn <- freshString "minor"
  let resIdx  = map (renE r1) (drop np cres)
      ctorApp = CExpr [] [] (CSpine cn (parRefs ++ fRefs))
      minorT  = CExpr (flds ++ ihDs) [] (CSpine mN (resIdx ++ [ctorApp]))
  return (Just (MinorInfo cn (typed mn minorT) fRefs recs))
  where
    recField f = case typ f of
      Just (CExpr xs _ (CSpine h fargs)) | h == dn -> do
        (xs', r2) <- freshTel Map.empty xs
        xRefs <- mapM varE xs'
        let idxs = map (renE r2) (drop np fargs)
            fApp = CExpr [] [] (CSpine (name f) xRefs)
        return [(xs', idxs, fApp)]
      _ -> return []
mkMinor _ _ _ _ _ _ = return Nothing

-- | np = nombre de paramètres, dd = déclaration du datatype, ctors = constructeurs convertis.
mkRecursor :: Int -> CDecl -> [CDecl] -> TCM (Maybe (CDecl, Sig))
mkRecursor np (CDecl dn (Just (CExpr dps _ _)) _) ctors = do
  let rn = dn ++ ".rec"
  lN <- freshString "l"
  mN <- freshString "motive"
  tN <- freshString "t"
  (pars, rP) <- freshTel Map.empty (take np dps)
  (mIdx, _)  <- freshTel rP (drop np dps)     -- indices locaux au motif
  (idxR, _)  <- freshTel rP (drop np dps)     -- indices du récurseur
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
      eqs <- mapM (\i -> do
                cpW  <- mapM wild pars
                idxW <- mapM wild idxR
                let pat = CExpr [] [] (CSpine (miCtor i) (cpW ++ miFields i))
                    lhs = CSpine rn (common ++ idxW ++ [pat])
                    ihs = [ CExpr xs [] (CSpine rn (common ++ ix ++ [fa])) | (xs, ix, fa) <- miRecs i ]
                    rhs = CSpine (name (miDecl i)) (miFields i ++ ihs)
                return (CEquation lhs rhs True)) infos
      let hid = Param `flip` Hidden
          exp' = Param `flip` NotHidden
          sig = [hid (declArity lD)] ++ map (hid . declArity) pars
             ++ [exp' (declArity motive)] ++ map (exp' . declArity) minorDs
             ++ map (hid . declArity) idxR ++ [exp' (declArity majD)]
      return (Just (CDecl rn (Just recTy) eqs, sig))
mkRecursor _ _ _ = return Nothing

gatherDatatypeInformations :: QName -> [String] -> [CDecl] -> Seen
                           -> TCM ([CDecl], Seen)
gatherDatatypeInformations qn bindnames lets ald =
  if nameToString qn `member` ald then return (lets, ald)
  else do
    def <- getConstInfo qn
    sym <- globalSym qn
    let alrd = insert (nameToString qn) (symDecl sym) ald
    let eqs = if nameToString qn == "_⊔_" then levelMaxEqs else []
    (ty', lets1, ald1, _) <- toCDecl (unEl (defType def)) (nameToString qn) eqs bindnames lets alrd False mempty
    let letss = ty' : lets1
    case theDef def of
      DatatypeDefn dd@DatatypeData { _dataCons = cons } -> do
        defs <- mapM getConstInfo cons
        syms <- mapM globalSym cons
        let names = map nameToString cons
            tys   = zip (map (unEl . defType) defs) names
            alrd2 = foldl (\m (k, s) -> insert k (symDecl s) m) ald1 (zip names syms)
        (ctys, lets2, ald2) <- foldlM (\(acc, ls, al) (t, n) -> do
                                  (nt, ls', al', _) <- toCDecl t n [] bindnames ls al False mempty
                                  return (nt : acc, ls', al'))
                                ([], letss, alrd2) tys
        let ctorDs = reverse ctys
        lq <- fromMaybe __IMPOSSIBLE__ <$> getName' BuiltinLevel
        (lets3, ald3) <- gatherDatatypeInformations lq [] lets2 ald2
        mrec <- mkRecursor (_dataPars dd) ty' ctorDs
        case mrec of
          Nothing        -> return (ctorDs ++ lets3, ald3)
          Just (recD, s) -> return (recD : ctorDs ++ lets3, insert (name recD) s ald3)
      FunctionDefn FunctionData { _funClauses = cls } -> do
        (eqs, lets2, ald2) <- clausesToEquations qn (symDecl sym) cls lets1 ald1
        return (ty' { equations = eqs } : lets2, ald2)
      _ -> return (letss, ald1)



-- | Les lemmes donnés en option sont ajoutés au contexte avant les variables locales.
produceCanonicalGoal :: [QName] -> Telescope -> Type -> [([(Term, Bool)], Term)] -> TCM (CDecl, GoalInfo)
produceCanonicalGoal lemmas ctx ty bds = do
  (lets0, ald0) <- foldlM (\(l, a) q -> gatherDatatypeInformations q [] l a)
                          ([typeDecl], Map.fromList [("Type", [Param 0 NotHidden])]) lemmas
  aux ctx ty [] lets0 ald0 mempty
  where
    aux :: Telescope -> Type -> [String] -> [CDecl] -> Seen -> Map String Sig
        -> TCM (CDecl, GoalInfo)
    aux ctx ty bindnames lets ald art =
      case ctx of
        EmptyTel -> do
          (res, _, ald', art') <- toCDecl (unEl ty) "Goal" [] bindnames lets ald True art
          return (res, GoalInfo ald' art' bindnames)
        ExtendTel dom (Abs nb b) ->
          case unEl ty of
            Pi d codom -> do
              (domdecl, lets', ald', art') <- toCDecl (unEl $ unDom dom) nb [] bindnames lets ald False art
              aux b (unAbs codom) (nb : bindnames) (domdecl : lets') ald' art'
            _ -> __IMPOSSIBLE__
        _ -> __IMPOSSIBLE__


{-
  The function called by C-c C-g.
-}

-- | Nom désigné par un lemme donné en option (définition, constructeur ou projection).
lemmaName :: A.Expr -> Maybe QName
lemmaName e = case e of
  A.ScopedExpr _ e' -> lemmaName e'
  A.Def' q _        -> Just q
  A.Con c           -> Just (A.headAmbQ c)
  A.Proj _ p        -> Just (A.headAmbQ p)
  _                 -> Nothing

call_canonical :: MonadTCM tcm => Rewrite -> InteractionId -> Range -> String -> tcm CanonicalResult
call_canonical norm ii rng args =
  case parseCanonicalOptions args of
    Left err   -> return . CanonicalExpr $ "Canonical : " ++ err ++ "\n" ++ canonicalUsage
    Right opts -> do
      -- Les noms inconnus provoquent l'erreur de portée habituelle d'Agda.
      lemmas <- liftTCM $ forM (optLemmas opts) $ \l -> (,) l . lemmaName <$> parseExprIn ii rng l
      case [ l | (l, Nothing) <- lemmas ] of
        [] -> call_canonical' ii opts [ q | (_, Just q) <- lemmas ]
        bad -> return . CanonicalExpr $
          "Canonical : ces lemmes ne sont pas des noms de définitions : " ++ unwords bad

call_canonical' :: MonadTCM tcm => InteractionId -> CanonicalOptions -> [QName] -> tcm CanonicalResult
call_canonical' ii opts lemmas = do
  bds <- liftTCM . withInteractionId ii $  do
      ip <- lookupInteractionPoint ii
      let l = Map.toList . getBoundary $ ipBoundary ip
      as <- getContextArgs
      let go (im, rhs) = do
            let rhs' = rhs `apply` as
            eqns <- forM (IntMap.toList im) $ \(a, b) -> do
                let a' = Var a []
                return (a', b)
            return (eqns, rhs')
      traverse go l
  -- Get the type of the goal
  ty <- liftTCM $ do
    metaId <- lookupInteractionId ii
    getMetaTypeInContext metaId
  -- Get the context of the goal
  ctx <- liftTCM $ withInteractionId ii getContextTelescope
  -- Name of the function containing the hole (for recursive calls)
  self <- liftTCM $ do
    ip <- lookupInteractionPoint ii
    return $ case ipClause ip of
      IPClause { ipcQName = q } -> nameToString q
      IPNoClause                -> "rec"
  -- Produce a goal for Canonical
  (goal', info) <- liftTCM $ produceCanonicalGoal lemmas ctx ty bds
  -- Add special constructors for Cubical equality in the context (only if equalities appear in the goal type)
  -- goal' <- case goal of
  --           CDecl n (Just (CExpr p l s)) e ->
  --             let nl = if "_≡_" `member` ald then l ++ [mpDecl , dpDecl] else l in
  --             return $ CDecl n (Just $ CExpr p nl s) e
  --           _ -> __IMPOSSIBLE__
  -- let goal' = testGoal
  let ctxDecls = maybe [] lets (typ goal')
  -- Call to Canonical
  results <- liftIO $ runCanonical goal' (optTimeout opts) (optCount opts)
  let pp = cexprToAgda info ctxDecls self
      fres = case results of
        []  -> "\nNo solution found."
        [d] -> "\n--- Hint :\n" ++ pp d
        ds  -> "\n--- Hints :\n" ++ unlines [ show i ++ ". " ++ pp d | (i, d) <- zip [1 :: Int ..] ds ]
  return . CanonicalExpr $ show goal' {-++ "\n\n--- Boundaries :\n" ++ P.prettyShow bds --}  ++ "\n" ++ fres
