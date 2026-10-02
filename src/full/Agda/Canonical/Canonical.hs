
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Agda.Canonical.Canonical where

import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.Aeson (decode, encode, Value (String))
import Data.ByteString (packCString, useAsCString)
import Data.ByteString.Lazy (fromStrict, toStrict)
import Data.Foldable (foldlM)
import Data.Map (Map, fromList, insert, member, toList)
import Data.Word (Word64)
import Foreign.C (CString)

import Agda.Canonical.Types
import Agda.Interaction.Base (Rewrite)
import Agda.Syntax.Common (Arg (unArg), InteractionId, NameId (NameId))
import Agda.Syntax.Common.Pretty qualified as P
import Agda.Syntax.Internal
import Agda.Syntax.Position (Range)
import Agda.TypeChecking.Level (reallyUnLevelView)
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Context (getContextTelescope, getContextArgs)
import Agda.TypeChecking.Monad.MetaVars
import Agda.TypeChecking.Monad.Signature (HasConstInfo (getConstInfo))
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Maybe (liftMaybe, fromMaybe)
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Telescope (teleNames)
import Text.PrettyPrint.Boxes (para)
import Text.PrettyPrint (TextDetails(Str))
import Agda.TypeChecking.Substitute.Class (Apply(apply))
import Agda.Utils.Monad (forM)


import Control.Monad (foldM, replicateM, zipWithM)
import Agda.TypeChecking.Monad.Context (underAbstraction)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope (teleNames, telView)
import Agda.Utils.Size (size)

import qualified Data.Map as Map
import qualified Data.IntMap as IntMap

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




{-
  Foreign function that calls Canonical.
-}
foreign import ccall "canonical" canonical :: CString -> Word64 -> Word64 -> IO CString

freshString :: MonadFresh NameId m => String -> m String
freshString s = do
  NameId n _ <- fresh
  return (s ++ "." ++ show n)

{-
  Converts a qualified name of Agda into a string.
-}
nameToString :: QName -> String
nameToString = P.prettyShow <$> qnameName




-- | Arité du type de chaque paramètre ; length = arité du symbole.
type Sig = [Int]

data Sym = Sym { symSig :: Sig, symTy :: Maybe Type }

arityOf :: Term -> Int
arityOf (Pi _ b) = 1 + arityOf (unEl (unAbs b))
arityOf _        = 0

-- | Signature syntaxique (variables liées).
termSig :: Term -> Sig
termSig (Pi a b) = arityOf (unEl (unDom a)) : termSig (unEl (unAbs b))
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
      return (size d : rest)

-- | Constructeurs : paramètres du datatype absents des elims, donc retirés.
--   Pas de type conservé pour eux (cf. limites).
globalSym :: QName -> TCM Sym
globalSym q = do
  def <- getConstInfo q
  sg  <- tySig (defType def)
  return $ case theDef def of
    ConstructorDefn cd -> Sym (drop (_conPars cd) sg) Nothing
    _                  -> Sym sg (Just (defType def))

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

simpleTy :: CExpr
simpleTy = CExpr [] [] (CSpine "Type" [simpleExpr "lzero"])   -- à adapter à ta convention pour Type

typed :: String -> CExpr -> CDecl
typed n t = CDecl n (Just t) []

eta1 :: String -> CExpr          -- λy. n y
eta1 n = CExpr [CDecl "y" Nothing []] [] (CSpine n [simpleExpr "y"])

piDecls :: [CDecl]
piDecls =
  [ CDecl "Pi"
      (Just $ CExpr [typed "A" simpleTy, typed "B" famT] [] (CSpine "Type" [simpleExpr "lzero"])) []
  , CDecl "Pi.mk"
      (Just $ CExpr [typed "A" simpleTy, typed "B" famT, typed "f" fnT] []
                    (CSpine "Pi" [simpleExpr "A", eta1 "B"])) []
  , CDecl "Pi.f"
      (Just $ CExpr [typed "A" simpleTy, typed "B" famT, typed "p" piAB, typed "a" (simpleExpr "A")] []
                    (CSpine "B" [simpleExpr "a"]))
      [ CEquation
          (CSpine "Pi.f" [ simpleExpr "A", eta1 "B"
                         , CExpr [] [] (CSpine "Pi.mk" [simpleExpr "A", eta1 "B", eta1 "g"])
                         , simpleExpr "a" ])
          (CSpine "g" [simpleExpr "a"]) True ]
  ]
  where
    famT = CExpr [typed "x" (simpleExpr "A")] [] (CSpine "Type" [simpleExpr "lzero"])
    fnT  = CExpr [typed "a" (simpleExpr "A")] [] (CSpine "B" [simpleExpr "a"])
    piAB = CExpr [] [] (CSpine "Pi" [simpleExpr "A", eta1 "B"])

withPi :: [CDecl] -> Map String Bool -> ([CDecl], Map String Bool)
withPi lets ald
  | "Pi" `member` ald = (lets, ald)
  | otherwise         = (piDecls ++ lets, insert "Pi" True ald)

-- | Pi a b en position de terme  ->  (A, λx. B), avec Pi déclaré dans le contexte.
piParts :: Dom Type -> Abs Type -> [String] -> [CDecl] -> Map String Bool -> Map String Sig
        -> TCM (CExpr, CExpr, [CDecl], Map String Bool)
piParts a b names lets ald art = do
  (nm, names') <- case b of
    NoAbs _ _ -> (\n -> (n, names))      <$> freshString "a"
    Abs n _   -> (\n' -> (n', n' : names)) <$> freshString n
  (ea, lets1, ald1) <- toCExpr (unEl $ unDom a) names [] lets ald False False art
  let art' = Map.insert nm (termSig (unEl $ unDom a)) art
  (eb, lets2, ald2) <- toCExpr (unEl $ unAbs b) names' [CDecl nm Nothing []] lets1 ald1 False False art'
  let (lets3, ald3) = withPi lets2 ald2
  return (ea, eb, lets3, ald3)

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

-- | Ajuste un argument à l'arité k attendue :
--   moins de paramètres -> η-expansion ; plus -> Pi.mk (types tirés du type attendu).
fixArg :: [String] -> Int -> Maybe Term -> CExpr -> [CDecl] -> Map String Bool -> Map String Sig
       -> TCM (CExpr, [CDecl], Map String Bool)
fixArg names k mty ce@(CExpr ps ls sp) lets ald art
  | m == k = return (ce, lets, ald)
  | m < k  = do
      ce' <- etaExtend (k - m) ce
      return (ce', lets, ald)
  | otherwise =
      case mty >>= stripPi (map name outer) names of
        Just (names', Pi dom b) -> do
          (ea, eb, lets1, ald1) <- piParts dom b names' lets ald art
          (inner', lets2, ald2) <- fixArg names' 1 (Just (Pi dom b)) (CExpr inner [] sp) lets1 ald1 art
          return (CExpr outer ls (CSpine "Pi.mk" [ea, eb, inner']), lets2, ald2)
        _ -> return (ce, lets, ald)   -- type attendu non syntaxiquement un Pi : inchangé
  where
    m = length ps
    (outer, inner) = splitAt k ps

-- | Applique une tête à ses arguments :
--   n < arité  -> η-expansion (paramètres renvoyés pour le CExpr englobant) ;
--   n > arité  -> Pi.f sur les arguments en excès ;
--   chaque argument est ajusté à son arité par fixArg.
applyHead :: String -> Maybe Sym -> [Term] -> [CExpr] -> [String] -> [CDecl]
          -> Map String Bool -> Map String Sig
          -> TCM (CSpine, [CDecl], [CDecl], Map String Bool)
applyHead hd Nothing _ cargs _ lets ald _ =
  return (CSpine hd cargs, [], lets, ald)
applyHead hd (Just (Sym sg mty)) terms cargs names lets0 ald0 art = do
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
            (ea, eb, ls1, al1) <- piParts dom b names ls al art
            (ce', ls2, al2)    <- fixArg names (arityOf dty) (Just dty) ce ls1 al1 art
            return (CSpine "Pi.f" [ea, eb, CExpr [] [] g, ce'], ls2, al2)
          _ -> return (appendArg g ce, ls, al)
  (fixed, lets1, ald1) <- foldM fixStep ([], lets0, ald0) (zip3 [0 ..] sg cargs)
  xs   <- replicateM (max 0 (ar - n)) (freshString "x")
  etas <- zipWithM etaVar xs (drop n sg)
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
           Map String Bool -> -- ^ already seen definitions / constructors
           Bool -> -- ^ is at top level
           Map String Sig -> -- ^ arities
           TCM (CDecl, [CDecl], Map String Bool, Map String Sig)
-- toCDecl t name eqs bindnames lets ald tplvl art = do
--   (typ, lets, ald, arity) <- toCExpr t bindnames [] lets ald tplvl True art
--   -- inlinePaths typ name eqs lets ald
--   return $ (CDecl {
--         name,
--         typ = Just typ,
--         equations = eqs
--   }, lets, ald, insert name arity art)

toCDecl t name eqs bindnames lets ald tplvl art = do
  (typ, lets, ald) <- toCExpr t bindnames [] lets ald tplvl True art
  return (CDecl { name, typ = Just typ, equations = eqs }, lets, ald, insert name (termSig t) art)
--
-- inlinePaths :: CExpr ->
--                 String ->
--                 [CEquation] ->
--                 [CDecl] ->
--                 Map String Bool ->
--                 TCM (CDecl, [CDecl], Map String Bool)
-- inlinePaths typ name eqs lets ald = do
--   case typ of
--     CExpr bds l (CSpine "_≡_" [_, a, x, y]) -> do
--       let sa = ets a
--           eq1 = CEquation (CSpine name (dte bds ++ [simpleExpr "i0"])) (ets x) True
--           eq2 = CEquation (CSpine name (dte bds ++ [simpleExpr "i1"])) (ets y) True
--       fi <- freshString "i"
--       return $ (
--         CDecl {
--             name,
--             typ = Just $ (CExpr (bds ++ [CDecl fi (Just $ simpleExpr "I") []]) l sa),
--             equations = [eq1, eq2]
--           }, lets, ald)
--     _ ->
--       return $ (CDecl {
--             name,
--             typ = Just typ,
--             equations = eqs
--       }, lets, ald)
--
-- dte :: [CDecl] -> [CExpr]
-- dte dl = map (simpleExpr . name) dl
--
-- ets :: CExpr -> CSpine
-- ets e =
--   case e of
--     CExpr [] [] s -> s
--     _ -> __IMPOSSIBLE__
--
{-
  This function converts an Agda term into a Canonical expression.
-}

toCExpr :: Term -> -- ^ The term to convert
           [String] -> -- ^ Bound names
           [CDecl] -> -- ^ Pi declarations
           [CDecl] -> -- ^ Context
           Map String Bool -> -- ^ already seen constructors / definitions
           Bool -> -- ^ is at top level
           Bool -> -- ^ to type ?
           Map String Sig -> -- ^ Arities
           TCM (CExpr, [CDecl], Map String Bool)
-- toCExpr t bindnames pidecl letdecl ald tplvl totyp art =
--   case t of
--     Pi a b -> do
--       -- Some Pi terms bind a name in their codomain.
--       -- If they do, we have to add the bound name to `bindnames`
--       -- for de Bruijn indices to be converted to the right string.
--       (newnames, na) <- do case b of
--                             NoAbs _ _ -> do
--                               n' <- freshString "a"
--                               return (bindnames, n')
--                             Abs n _ -> do
--                               n' <- freshString n
--                               return (n' : bindnames, n')
--       -- if totyp  then do
--       -- We convert the domain into a CDecl and add it to `pidecl`
--       (domdecl, lets, ald, art) <- toCDecl (unEl $ unDom a) na [] bindnames letdecl ald False art
--       -- Convert the codomain into a Canonical expression
--       (e, d,a,i) <- toCExpr (unEl $ unAbs b) newnames (domdecl : pidecl) lets ald tplvl totyp art
--       return (e, d, a, i + 1)
--       -- else do
--       --   (ea, lets, ald) <- toCExpr (unEl $ unDom a) bindnames pidecl letdecl ald False False
--       --   ((CExpr truc0 truc1 truc2), lets, ald) <- toCExpr (unEl $ unAbs b) newnames pidecl letdecl ald False False
--       --   return $ (CExpr {
--       --       params = [],
--       --       lets = [],
--       --       spine = CSpine "Canonical.PiTypeType" [simpleExpr "lzero", simpleExpr "lzero", ea, CExpr ((CDecl na Nothing []) : truc0) truc1 truc2]
--       --     }, lets, ald)
--     Lam a b -> do
--       let (newnames, name) = case b of
--                       NoAbs _ _ -> (bindnames, "_")
--                       Abs n _ -> (n : bindnames, n)
--       (e, d, a, i) <- toCExpr (unAbs b) newnames (CDecl name Nothing [] : pidecl ) letdecl ald tplvl False art
--       return (e, d, a, 0)
--     _ -> do
--       -- If we are not converting a Pi, we have to convert the term into a spine.
--       (spine, lets, ald) <- toCSpine t bindnames letdecl ald art
--       -- Then we build the Canonical expression by putting together `pidecl`,
--       -- `letdecl` and the spine
--       return $ (
--         CExpr {
--             params = reverse pidecl,
--             -- We want to add the context only if we are building the top-level CExpr.
--             lets = if tplvl then reverse lets else [],
--             spine
--           }, lets, ald, 0)
toCExpr t bindnames pidecl letdecl ald tplvl totyp art =
  case t of
    Pi a b | totyp -> do
      (newnames, na) <- case b of
        NoAbs _ _ -> do n' <- freshString "a"; return (bindnames, n')
        Abs n _   -> do n' <- freshString n;   return (n' : bindnames, n')
      (domdecl, lets, ald, art) <- toCDecl (unEl $ unDom a) na [] bindnames letdecl ald False art
      toCExpr (unEl $ unAbs b) newnames (domdecl : pidecl) lets ald tplvl totyp art
      -- return (e, d, a', i + 1)
    Pi a b -> do
      (ea, eb, lets, ald) <- piParts a b bindnames letdecl ald art
      return ( CExpr (reverse pidecl) (if tplvl then reverse lets else []) (CSpine "Pi" [ea, eb])
             , lets, ald )
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

{-
  This function converts an Agda term to a Canonical spine.
-}

-- toCSpine :: Term -> -- ^ The term to convert
--             [String] -> -- ^ Bound names
--             [CDecl] -> -- ^ Context
--             Map String Bool -> -- ^ Already seen constructors / datatypes
--             Map String Int -> -- ^ Arities
--             TCM (CSpine, [CDecl], Map String Bool)
-- toCSpine t bindnames lets ald art =
--   case t of
--     -- On a variable applied to multiple arguments.
--     Var i el -> do
--       -- We convert the arguments into Canonical expressions.
--       (args, lets, ald) <- elimsToCExpr el bindnames lets ald art
--       return $ (
--         CSpine {
--           head = bindnames !! i, -- We put the variable at the head of the spine.
--           args  -- And put the converted arguments.
--          }, lets, ald)
--     -- When we encounter a term 'Set l'
--     Sort (Type l) -> do
--       -- We convert the level into a term
--       t' <- reallyUnLevelView l
--       -- convert the term into a Canonical expression.
--       (arg, lets, ald, _) <- toCExpr t' bindnames [] lets ald False False art
--       return $ (
--         -- Build the spine
--         CSpine {
--           head = "Type",
--           args = [arg]
--         }, lets, ald)
--     Sort (SSet l) -> do
--       -- We convert the level into a term
--       t' <- reallyUnLevelView l
--       -- convert the term into a Canonical expression.
--       (arg, lets, ald, art) <- toCExpr t' bindnames [] lets ald False False art
--       return $ (
--         -- Build the spine
--         CSpine {
--           head = "ß",
--           args = [arg]
--         }, lets, ald)
--
--     Sort (IntervalUniv) ->
--       return $ (
--         CSpine {
--             head = "IUniv",
--             args = []
--           }, lets, ald)
--
--     -- On a level alone
--     Level l -> do
--       -- First convert the level into a term
--       t' <- reallyUnLevelView l
--       -- Then convert the term into a spine
--       toCSpine t' bindnames lets ald art
--
--     -- On a datatype name applied to arguments
--     Def qname e -> do
--       -- We first convert the arguments into Canonical expressions
--       (args, lets, ald) <- elimsToCExpr e bindnames lets ald art
--       -- Then we add all the information related to the datatype to the context.
--       (lets, ald) <- gatherDatatypeInformations qname bindnames lets ald
--       -- And create the spine
--       return $ (
--         CSpine {
--           head = P.prettyShow (qnameName qname),
--           args
--         }, lets, ald)
--
--     -- When treating a constructor applied to arguments.
--     Con hd _ e -> do
--       -- We get its datatype
--       infos <- getConstInfo (conName hd)
--       let dataname = case theDef infos of
--                     ConstructorDefn cd -> _conData cd
--                     _ -> __IMPOSSIBLE__
--       -- Convert the arguments into Canonical expressions.
--       (args, lets, ald) <- elimsToCExpr e bindnames lets ald art
--       -- Add all the definitions of the datatype.
--       (lets, ald) <- gatherDatatypeInformations dataname bindnames lets ald
--       -- Build the spine
--       return $ (
--         CSpine {
--           head = P.prettyShow . qnameName $ conName hd,
--           args
--         }, lets, ald)
--
--     -- Unhandled cases
--     e -> return $ (
--       CSpine {
--         head = P.prettyShow e,
--         args = []
--       }, lets, ald)
toCSpine :: Term -> [String] -> [CDecl] -> Map String Bool -> Map String Sig
         -> TCM (CSpine, [CDecl], [CDecl], Map String Bool)
toCSpine t bindnames lets ald art =
  case t of
    Var i el -> do
      (args, lets, ald) <- elimsToCExpr el bindnames lets ald art
      let h = bindnames !! i
      applyHead h (flip Sym Nothing <$> Map.lookup h art) (appliedTerms el) args bindnames lets ald art
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
                Map String Bool -> -- Already seen datatypes / constructors
                Map String Sig -> -- ^ Arities
                TCM ([CExpr], [CDecl], Map String Bool)
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
                 Map String Bool -> -- Already seen datatypes / constructors
                 Map String Sig -> -- Arities
                 TCM (CExpr, [CDecl], Map String Bool)
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

{-
  This function gathers all the information about a datatype (its type, its constructors),
  converts it into Canonical declarations and puts it in the context.
-}
--
-- getCubicalDefs :: [CDecl] ->
--                   Map String Bool ->
--                   TCM ([CDecl], Map String Bool)
-- getCubicalDefs lets ald =
--   let blist = [ BuiltinPath,
--                 BuiltinPathP,
--                 BuiltinIntervalUniv,
--                 BuiltinInterval,
--                 BuiltinIZero,
--                 BuiltinIOne,
--                 -- BuiltinPartial,
--                 -- BuiltinPartialP,
--                 BuiltinIsOne,
--                 BuiltinIsOne1,
--                 BuiltinIsOne2,
--                 -- BuiltinSub,
--                 -- BuiltinIsOneEmpty,
--                 BuiltinItIsOne ]
--       plist = [ PrimLevelMax]
--                 -- PrimSubOut]
--                 -- PrimPartial,
--                 -- PrimPartialP ]
--                 -- PrimSubOut,
--                 -- PrimPOr,
--                 --PrimHComp ]
--   in
--   do
--     qnameblist <- mapM (fmap (fromMaybe __IMPOSSIBLE__) . getName') blist
--     qnameplist <- mapM (fmap (fromMaybe __IMPOSSIBLE__) . getName') plist
--     (lets, ald) <- foldlM (\(l, a) n ->  gatherDatatypeInformations n [] l a) (lets, ald) (qnameblist ++ qnameplist )
--     return (lets, ald)
--

-- clauseToEquation :: QName ->
--                     Clause ->
--                     [CDecl] ->
--                     Map String Bool ->
--                     TCM (CEquation, [CDecl], Map String Bool)
-- clauseToEquation name cls lets ald =
--   let boundnames = reverse . teleNames $ clauseTel cls
--       lhs = dummyCSpine
--   in
--   case (clauseBody cls) of
--     Just t -> do
--       (rhs, lets, ald) <- toCSpine t boundnames lets ald
--       return $ (CEquation lhs rhs True, lets, ald)
--     _ -> __IMPOSSIBLE__
--
-- clausesToEquations :: QName ->
--                       [Clause] ->
--                       [CDecl] ->
--                       Map String Bool ->
--                       TCM ([CEquation], [CDecl], Map String Bool)
-- clausesToEquations n cls lets ald =
--   case cls of
--     [] -> return ([], lets, ald)
--     c : cll -> do
--       (eqs, lets, ald) <- clausesToEquations n cll lets ald
--       (eq, lets, ald) <- clauseToEquation n c lets ald
--       return (eq : eqs, lets, ald)

gatherDatatypeInformations :: QName -> -- ^ The name of the datatype
                              [String] -> -- ^ Bound names
                              [CDecl] -> -- ^ Context
                              Map String Bool -> -- ^ Already seen datatypes / constructors
                              TCM ([CDecl], Map String Bool)
gatherDatatypeInformations qn bindnames lets ald =
  -- If the datatype was already seen, we don't have to do anything
  if ((nameToString  qn) `member` ald) then return (lets, ald)

  else do
    -- We add the new datatype to the already-seen list
    let alrd = insert (nameToString qn) True ald
    -- Gather its information
    def <- getConstInfo qn
    -- Get its type
    let ty      = defType def
    --     clauses = defClauses def
    --
    -- (eqs, lets, ald) <- clausesToEquations qn clauses lets ald
    -- let eqs = case (nameToString qn) of
    --             -- "primHComp" -> primHCompEquations
    --             "_⊔_" -> primLevelMaxEquations
    --             -- "Partial" -> partialEquations
    --             -- "PartialP" -> partialPEquations
    --             "_≡_" -> eqEquations
    --             -- "primPOr" -> primPOrEquations
    --             _ -> []
    -- Convert the type
    (ty, lets, ald, art) <- toCDecl (unEl ty) (nameToString qn) [] bindnames lets alrd False mempty
    -- Add the converted type to the context
    let letss = ty : lets
    -- And gather the information about the constructors
    case theDef def of
      DatatypeDefn DatatypeData { _dataCons = cons } -> do
        -- Get all the constructor names and their information
        defs <- mapM getConstInfo cons

        -- Convert all the types of the constructors to declarations
        let tys = zip (map (unEl . defType) defs) (map nameToString cons)
        let alrd = foldl (\m k -> insert k True m ) ald (map nameToString cons)
        (ctys, lets, ald) <- foldlM (\(acc, lets, ald) (t, n) -> do
                                (nt, lets, ald, art) <- toCDecl t n [] bindnames lets ald False art
                                return (nt : acc, lets, ald))
                                ([], letss, alrd) tys
        -- Add the declarations to the context
        let lts = (reverse $ ctys) ++ lets
        return (lts, ald)
      -- Unhandled case
      _ -> return (letss , ald)

{-
  This function produces a goal for Canonical from an Agda context telescope and an Agda type.
  For now, when we convert a goal type, its context is folded into it.
  We have to unfold the context and add it to the Canonical context.
-}
produceCanonicalGoal :: Telescope -> -- ^ Context telescope
                        Type ->  -- ^ The actual goal
                        [([(Term, Bool)], Term)] -> -- ^ Boundaries ?
                        TCM CDecl
produceCanonicalGoal ctx ty bds =
  -- Add handmade declarations for Cubical
  let -- decls = [outSDecl, inSDecl,subDecl, primHCompDecl, primPOrDecl, {-cpittfDecl, cpittmkDecl, cpittDecl, cpistfDecl, cpistmkDecl,cpistDecl,-} orDecl, andDecl, negDecl, ssetDecl, typeDecl]
      decls = [typeDecl]
      -- ald = fromList [("primHComp", True), ("primINeg", True), ("primIMin", True), ("primIMax", True)]
      ald = mempty
      art = mempty
  in
  do
  -- (decls , ald) <- getCubicalDefs decls ald
  (decl, names) <- aux ctx ty []  decls ald art
  -- (CDecl n t eq) <- refoldNecessary decl bds
  -- eqs <- createConstraints (CDecl n t eq) bds names
  -- return $ CDecl n t (eq)
  return decl
    where
      {-
        This function unfolds a telescope, converts its elements to declarations, and adds them to the Canonical context.
      -}
      aux :: Telescope -> -- The context telescope
            Type -> -- The type to convert
            [String] -> -- Bound names
            [CDecl] ->  -- Canonical context
            Map String Bool -> -- Already seen datatypes / constructors
            Map String Sig-> -- Arity
            TCM (CDecl, [String])
      aux ctx ty bindnames lets ald art=
        case ctx of
          -- If the telescope is empty, we just have to convert the type
          EmptyTel -> do
            (res, _, _, _) <- toCDecl (unEl ty) "Goal" [] bindnames lets ald True art
            return (res, bindnames)
          -- Otherwise our goal type should be of the form `Pi _ _`
          ExtendTel dom (Abs nb b) ->
            case unEl ty of
              -- We unfold the context
              Pi d codom -> do
                -- Convert the type of the first element of the telescope
                (domdecl, lets, ald, art) <- toCDecl (unEl $ unDom dom) nb [] bindnames lets ald False art
                -- Convert the rest
                aux b (unAbs codom) (nb : bindnames) (domdecl : lets) ald art
              _ -> __IMPOSSIBLE__
          _ -> __IMPOSSIBLE__

-- createConstraints :: CDecl ->
--                      [([(Term, Bool)], Term)] ->
--                      [String] ->
--                      TCM [CEquation]
-- createConstraints d c names =
--   case c of
--     [] -> return []
--     c : cs -> do
--       eqs <- createConstraints d cs names
--       eq <- createConstraint d c names
--       return (eq : eqs)
--
-- createConstraint :: CDecl ->
--                     ([(Term, Bool)], Term) ->
--                     [String] ->
--                     TCM CEquation
-- createConstraint d (aff, t) names =
--   let CSpine hd tl = fullApp d
--   in
--   do
--   (rhs, _, _) <- toCSpine t names [] mempty
--   return $ CEquation (CSpine hd (foldl changeArgs tl aff)) rhs True
--     where
--       toExp :: [CDecl] -> [CExpr]
--       toExp t =
--         case t of
--           [] -> []
--           (CDecl n _ _) : dl -> simpleExpr n : toExp dl
--
--       fullApp :: CDecl -> CSpine
--       fullApp (CDecl n (Just t) _) = CSpine n (toExp (params t))
--       fullApp _ = __IMPOSSIBLE__
--
-- changeArgs :: [CExpr] -> (Term, Bool) -> [CExpr]
-- changeArgs args (Var n _, b) = reverse (aux (reverse args) n b)
--   where
--     aux :: [CExpr] -> Int -> Bool -> [CExpr]
--     aux (a : args) 0 b = (if b then simpleExpr "i1" else simpleExpr "i0") : args
--     aux (a : args) n b = a : (aux args (n - 1) b)
--     aux _ _ _ = __IMPOSSIBLE__
--
-- changeArgs _ _ = __IMPOSSIBLE__
--
--
-- refoldNecessary :: CDecl ->
--                    [([(Term, Bool)], Term)] ->
--                    TCM CDecl
-- refoldNecessary d bds =
--   aux d (maxId bds)
--   where
--     maxId :: [([(Term, Bool)], Term)] -> Int
--     maxId [] = -1
--     maxId ((l, _) : ll) = max (maxId' l) (maxId ll)
--       where
--         maxId' :: [(Term, Bool)] -> Int
--         maxId' [] = -1
--         maxId' ((t, _) : ll) =
--           case t of
--             Var i _ -> max i (maxId' ll)
--             _ -> __IMPOSSIBLE__
--
--     aux :: CDecl -> Int -> TCM CDecl
--     aux d (-1) = return d
--     aux d n =
--       case d of
--         CDecl name (Just e) eqs ->
--           case e of
--             CExpr bd lts sp ->
--               case reverse lts of
--                 lt : lts -> aux (CDecl name (Just $ CExpr (lt : bd) (reverse lts) sp ) eqs) (n - 1)
--                 _ -> __IMPOSSIBLE__
--         _ -> __IMPOSSIBLE__
--

{-
  The function called by C-c C-g.
-}

call_canonical :: MonadTCM tcm => Rewrite -> InteractionId -> Range -> String -> tcm CanonicalResult
call_canonical norm ii rng args = do
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
  -- Produce a goal for Canonical
  goal' <- liftTCM $ produceCanonicalGoal ctx ty bds
  -- Add special constructors for Cubical equality in the context (only if equalities appear in the goal type)
  -- goal' <- case goal of
  --           CDecl n (Just (CExpr p l s)) e ->
  --             let nl = if "_≡_" `member` ald then l ++ [mpDecl , dpDecl] else l in
  --             return $ CDecl n (Just $ CExpr p nl s) e
  --           _ -> __IMPOSSIBLE__
  -- let goal' = testGoal
  liftIO $
    -- Call to Canonical
    useAsCString (toStrict (encode goal')) $ \ety -> do -- may be dangerous, have to check
    cres <- canonical ety 30 1
    cstr <- packCString cres
    results :: [CExpr] <- liftMaybe (decode (fromStrict cstr))
    fres <- case results of
            [] -> return "\nNo solution found."
            (d : _) -> return $ "\n--- Hint :\n" ++ (show d)
    return . CanonicalExpr $ show goal' {-++ "\n\n--- Boundaries :\n" ++ P.prettyShow bds --}  ++ "\n" ++ fres
