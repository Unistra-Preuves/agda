{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Agda.Canonical.Canonical where


import Data.Aeson
import Data.Maybe
import Data.String (IsString (fromString))
import Data.Word
import Foreign.C (CString, newCString, peekCString)
import GHC.Generics (Generic, C1)
import Agda.Canonical.Types
import Agda.Interaction.Base (Rewrite)
import Agda.TypeChecking.Pretty
import Agda.Syntax.Common (InteractionId, Arg (unArg, argInfo), Hiding (NotHidden), ArgInfo (argInfoHiding), makeInstance)

import Agda.Syntax.Common.Pretty qualified as P
import Agda.TypeChecking.Monad.Base (MonadTCM, TCM, liftTCM)
import Agda.Syntax.Position (Range)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Agda.TypeChecking.Monad.MetaVars
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.MetaVars (lookupInteractionId, lookupLocalMeta )
import Agda.TypeChecking.Monad.Context (getContextTelescope, getContextArgs)
import Agda.Utils.Impossible (impossible, __IMPOSSIBLE__)
import Agda.Utils.Maybe (liftMaybe)
import Agda.TypeChecking.Datatypes (getConstructors)
import Agda.TypeChecking.Monad.Signature (HasConstInfo(getConstInfo))
import Agda.Benchmarking (Phase(Definition))
import Agda.TypeChecking.Monad.Base
import Agda.Utils.Haskell.Syntax (DataOrNew(DataType), Literal (String))
import Agda.Syntax.Translation.AbstractToConcrete (ToConcrete(toConcrete))
import Agda.TypeChecking.Substitute (Apply(apply), piApply, domFromNamedArgName)
import Data.Foldable (foldlM)
import Data.ByteString.Lazy (fromStrict, toStrict )
import Data.ByteString (packCString, useAsCString)
import Data.Map (Map, member, insert)
import Text.PrettyPrint (TextDetails(Str))
import Agda.TypeChecking.Level (reallyUnLevelView)
import Data.Vector.Unboxed (DoNotUnboxNormalForm)

foreign import ccall "canonical" canonical :: CString -> CString -> Word64 -> Word64 -> IO CString

nameToString :: QName -> String
nameToString = P.prettyShow <$> qnameName

-- typeToCDecl :: Type -> -- Type to convert
--                [CDecl] ->  -- Pi bindings
--                [CDecl] ->  -- lets bindings
--                [String] ->  -- Names for variables
--                Map String Type -> -- Already seen data types
--                Bool -> -- toplevel?
--                TCM (CDecl, Map String Type, [CDecl]) -- Converted type along with all datatypes encountered
-- typeToCDecl t = toCDecl (unEl t)
--
-- toCSpine :: Term -> [String] -> [CDecl] -> Map String Type -> TCM (CSpine, Map String Type, [CDecl])
-- toCSpine t names lts alrdsn =
--   case t of
--     Var i e -> do
--       (args, alrdsn', lts') <-  elimsToCExpr e names lts alrdsn
--       return (CSpine {
--         head =  names !! i ,
--         args
--       }, alrdsn', lts')
--     Def qname e -> do
--       (args, alrdsn', lets') <- elimsToCExpr  e names lts alrdsn
--       (lt, ald) <- gatherDatatypeInformations qname lets' alrdsn' names
--       return (CSpine {
--           head = P.prettyShow (qnameName qname),
--           args
--         }, ald, lt)
--     Con hd _ e -> do
--       infos <- getConstInfo (conName hd)
--       let (dataname, pars) = case theDef infos of
--                     ConstructorDefn cd -> (_conData cd, _conPars cd)
--                     _ -> __IMPOSSIBLE__
--       (args, alrdsn', lts') <- elimsToCExpr e names lts alrdsn
--       (lt, ald) <- gatherDatatypeInformations dataname lts' alrdsn' names
--       return (CSpine {
--           head = P.prettyShow . qnameName $ conName hd,
--           args
--         }, ald, lt)
--     Sort (Type l) -> do
--       t' <- reallyUnLevelView l
--       (arg, alrdsn', lts') <- toCExpr t' names lts alrdsn
--       return (CSpine {
--           head = "Set",
--           args = [arg]
--         }, alrdsn', lts')
--     Sort s ->
--       return (CSpine {
--           head = P.prettyShow s,
--           args = []
--         }, alrdsn , lts)
--     Level l -> do
--       t' <- reallyUnLevelView l
--       toCSpine t' names lts alrdsn
--     Pi{} -> do
--       (cty, alrdsn', lts') <- toCDecl t [] lts names alrdsn False
--       return (CSpine {
--           head = "(" ++ show cty ++ ")",
--           args = []
--         }, alrdsn', lts')
--     _ -> return (CSpine{
--             head  = P.prettyShow t,
--             args  = []
--       }, alrdsn , lts)
--
-- toCDecl  :: Term ->
--             [CDecl] ->
--             [CDecl] ->
--             [String] ->
--             Map String Type ->
--             Bool -> -- TopLevel ?
--             TCM (CDecl, Map String Type, [CDecl])
-- toCDecl t bds lts names alrdsn tplvl =
--   case t of
--     Pi a (NoAbs nb b ) -> do
--       (domty, alrdsn', lts') <- (typeToCDecl (unDom a) [] lts names alrdsn) False -- (isImplicit a || prms > 0) 0) -- Convert domain type
--       typeToCDecl b ((nb , Just domty) : bds) lts' names alrdsn'  tplvl -- implicit (if prms > 0 then (prms  - 1) else 0)-- Convert  codomain type
--     Pi a b -> do
--       (domty, alrdsn', lts') <- typeToCDecl (unDom a) [] lts names alrdsn False -- (isImplicit a || prms > 0) 0
--       typeToCDecl (unAbs b) ((absName b, Just domty) : bds) lts' (absName b : names) alrdsn' tplvl  -- implicit (if prms > 0 then prms - 1 else 0)
--     Sort s -> do
--       (spine, alrdsns, lets) <- toCSpine t names lts alrdsn -- implicit       -- On defined names
--       return (CExpr {
--         params = reverse bds,
--         lets = if tplvl then reverse lts else [],
--         spine
--       }, alrdsns, lets)
--     Def qname el -> do
--       (expr, alrdsns, lets) <- toCExpr t names lts alrdsn -- implicit       -- On defined names
--       return (CExpr {
--         params = reverse bds,
--         lets = if tplvl then reverse lets else [],
--         spine
--       }, alrdsns, lets )
--     _ -> do
--       (spine, alrdsns, lets) <- toCSpine t names lts alrdsn  -- implicit    -- On defined names
--       return (CExpr {
--         params = reverse bds,
--         lets = if tplvl then reverse lets else [],
--         spine
--       }, alrdsns , lets)
--
-- elimsToCExpr ::  [Elim' Term] -> [String] ->  [CDecl] -> Map String Type -> TCM ([CExpr], Map String Type, [CDecl])
-- elimsToCExpr e names lts alrdsn =
--   case e of
--     [] -> return ([], alrdsn, lts)
--     el : els -> do
--       (el', alrdsn', lts' ) <- elimToCExpr el names lts alrdsn -- (pars > 0)
--       (els', alrdsn'', lts'') <- elimsToCExpr els names lts' alrdsn' -- (pars - 1)
--       return (el' : els', alrdsn'' , lts'')
--   where
--
--   elimToCExpr  ::  Elim' Term -> [String] ->  [CDecl] -> Map String Type -> TCM (CExpr, Map String Type, [CDecl])
--   elimToCExpr c names lts alrdsn = -- pars=
--     case c of
--       Apply t -> toCExpr (unArg t) names lts alrdsn  -- (pars || argInfoHiding (argInfo t) /= NotHidden)
--       e -> return (CExpr {
--           params = [],
--           lets = [],
--           spine = CSpine {
--               head = P.prettyShow e,
--               args = []
--             }
--         }, alrdsn, lts)
--
-- toCExpr :: Term -> [String] -> [CDecl] -> Map String Type -> TCM (CExpr, Map String Type, [CDecl])
-- toCExpr t names lts alrdsn = do
--   (spine, alrdsn', lets) <- toCSpine t names lts alrdsn
--   return (CExpr{
--     params = [],
--     lets = [],
--     spine
--   } , alrdsn', lets)
--
-- getConstParams :: Definition -> Int
-- getConstParams d =
--   case theDef d of
--     ConstructorDefn c -> _conPars c
--     _ -> __IMPOSSIBLE__
--
-- gatherDatatypeInformations :: QName -> [CDecl] -> Map String Type -> [String] -> TCM ([CDecl], Map String Type)
-- gatherDatatypeInformations qn lts alrdsn names =
--   if ((nameToString  qn) `member` alrdsn) then return (lts, alrdsn)
--   else do
--     def <- getConstInfo qn                                               -- gather its informations
--     let ty = defType def                                                 -- get it's type
--     let alrdsn' = insert (nameToString qn) ty alrdsn                                   -- we add the new encoutered type in the list
--     (tys, alr, letsss) <- (typeToCDecl ty [] lts names alrdsn' False )   -- convert it and add it to already seen types
--     let letss = tys : letsss
--     case theDef def of                                                   -- match on the kind of definition we have for the type
--       DatatypeDefn DatatypeData { _dataCons = cons } -> do               -- get all the type constructors names
--         defs <- mapM getConstInfo cons                                   -- get their informations
--         let tys = map (\d -> (defType d, getConstParams d)) defs
--         let ald = foldl (\m (k, v) -> insert k v m ) alr (zip (map nameToString  cons) (map fst tys))
--         (ctys, alrdsnes, lts'') <- foldlM (\(acc, alrdsn', lets) (t, p) -> do
--                                 (nt, alrdsns', lets') <- typeToCDecl t [] lets names alrdsn' False -- False p -- (cpt + 1000)
--                                 return (nt : acc, alrdsns', lets'))
--                                 ([], ald, letss) tys
--         let lteess = (reverse $ ctys) ++ lts''
--         return (lteess, alrdsnes)
--       _ -> return (letss , alr)
--
-- myZip :: [a] -> [b] -> [(a, b, [c])]
-- myZip [] [] = []
-- myZip (a : as) (b : bs) = (a, b, []) : myZip as bs
-- myZip _ _ = __IMPOSSIBLE__
--

toCDecl :: Term -> -- ^ The term to convert
           String -> -- ^ The name of the declaration
           [String] -> -- ^ already binded names
           [CDecl] -> -- ^ let declarations
           Map String Bool -> -- ^ already seen definitions / constructors
           Bool -> -- ^ is at toplevel
           TCM (CDecl, [CDecl], Map String Bool)
toCDecl t name bindnames lets ald tplvl = do
  (typ, lets, ald) <- toCExpr t bindnames [] lets ald tplvl
  return $ (
    CDecl {
        name,
        typ = Just typ,
        equations = []
      }, lets, ald)

toCExpr :: Term ->
           [String] ->
           [CDecl] ->
           [CDecl] ->
           Map String Bool ->
           Bool ->
           TCM (CExpr, [CDecl], Map String Bool)
toCExpr t bindnames pidecl letdecl ald tplvl =
  case t of
    Pi a b -> do
      let newnames = case b of
                      NoAbs _ _ -> bindnames
                      Abs n _ -> n : bindnames
      (domdecl, lets, ald) <- toCDecl (unEl $ unDom a) (absName b) bindnames letdecl ald False
      toCExpr (unEl $ unAbs b) newnames (domdecl : pidecl) lets ald tplvl
    _ -> do
      (spine, lets, ald) <- toCSpine t bindnames letdecl ald
      return $ (
        CExpr {
            params = reverse pidecl,
            lets = if tplvl then reverse lets else [],
            spine
          }, lets, ald)

toCSpine :: Term ->
            [String] ->
            [CDecl] ->
            Map String Bool ->
            TCM (CSpine, [CDecl], Map String Bool)
toCSpine t bindnames lets ald =
  case t of
    Var i el -> do
      (el, lets, ald) <- elimsToCExpr el bindnames lets ald
      return $ (
        CSpine {
          head = bindnames !! i,
          args = el
         }, lets, ald)
    Sort (Type l) -> do
      t' <- reallyUnLevelView l
      (arg, lets, ald) <- toCExpr t' bindnames [] lets ald False
      return $ (
        CSpine {
          head = "Set",
          args = [arg]
        }, lets, ald)
    Level l -> do
      t' <- reallyUnLevelView l
      toCSpine t' bindnames lets ald
    Def qname e -> do
      (args, lets, ald) <- elimsToCExpr e bindnames lets ald
      (lets, ald) <- gatherDatatypeInformations qname bindnames lets ald
      return $ (
        CSpine {
          head = P.prettyShow (qnameName qname),
          args
        }, lets, ald)
    Con hd _ e -> do
      infos <- getConstInfo (conName hd)
      let (dataname, pars) = case theDef infos of
                    ConstructorDefn cd -> (_conData cd, _conPars cd)
                    _ -> __IMPOSSIBLE__
      (args, lets, ald) <- elimsToCExpr e bindnames lets ald
      (lets, ald) <- gatherDatatypeInformations dataname bindnames lets ald
      return $ (
        CSpine {
          head = P.prettyShow . qnameName $ conName hd,
          args
        }, lets, ald)
    e -> return $ (
      CSpine {
        head = P.prettyShow e,
        args = []
      }, lets, ald)

elimsToCExpr :: [Elim' Term] ->
                [String] ->
                [CDecl] ->
                Map String Bool ->
                TCM ([CExpr], [CDecl], Map String Bool)
elimsToCExpr e names lets ald =
  case e of
    [] -> return ([], lets, ald)
    el : els -> do
      (el, lets, ald) <- elimToCExpr el names lets ald
      (els, lets, ald) <- elimsToCExpr els names lets ald
      return (el : els, lets, ald)
  where

  elimToCExpr :: Elim' Term ->
                 [String] ->
                 [CDecl] ->
                 Map String Bool ->
                 TCM (CExpr, [CDecl], Map String Bool)
  elimToCExpr c names lets ald =
    case c of
      Apply t -> toCExpr (unArg t) names [] lets ald False
      e -> return $ (
        CExpr {
          params = [],
          lets = [],
          spine = CSpine {
              head = P.prettyShow e,
              args = []
            }
        }, lets, ald)


gatherDatatypeInformations :: QName ->
                              [String] ->
                              [CDecl] ->
                              Map String Bool ->
                              TCM ([CDecl], Map String Bool)
gatherDatatypeInformations qn bindnames lets ald =
  if ((nameToString  qn) `member` ald) then return (lets, ald)
  else do
    def <- getConstInfo qn                                               -- gather its informations
    let ty = defType def                                                 -- get it's type
    let alrd = insert (nameToString qn) True ald                                   -- we add the new encoutered type in the list
    (ty, lets, ald) <- toCDecl (unEl ty) (nameToString qn) bindnames lets alrd False    -- convert it and add it to already seen types
    let letss = ty : lets
    case theDef def of                                                   -- match on the kind of definition we have for the type
      DatatypeDefn DatatypeData { _dataCons = cons } -> do               -- get all the type constructors names
        defs <- mapM getConstInfo cons                                   -- get their informations
        let tys = zip (map (unEl . defType) defs) (map nameToString cons)
        let alrd = foldl (\m k -> insert k True m ) ald (map nameToString cons)
        (ctys, lets, ald) <- foldlM (\(acc, lets, ald) (t, n) -> do
                                (nt, lets, ald) <- toCDecl t n bindnames lets ald False -- False p -- (cpt + 1000)
                                return (nt : acc, lets, ald))
                                ([], letss, alrd) tys
        let lts = (reverse $ ctys) ++ lets
        return (lts, ald)
      _ -> return (letss , ald)

produceCanonicalGoal :: Telescope -> Type -> TCM CDecl
produceCanonicalGoal ctx ty = aux ctx ty [] [] mempty
  where

  aux :: Telescope ->
         Type ->
         [String] ->
         [CDecl] ->
         Map String Bool ->
         TCM CDecl
  aux ctx ty bindnames lets ald =
    case ctx of
      EmptyTel -> do
        (res, _, _) <- toCDecl (unEl ty) "Goal" bindnames lets ald True
        return res
      ExtendTel dom (Abs nb b) ->
        case unEl ty of
          Pi d codom -> do
            (domdecl, lets, ald) <- toCDecl (unEl $ unDom dom) nb bindnames lets ald False
            aux b (unAbs codom) (nb : bindnames) (domdecl : lets) ald
          _ -> __IMPOSSIBLE__
      _ -> __IMPOSSIBLE__

call_canonical :: MonadTCM tcm => Rewrite -> InteractionId -> Range -> String -> tcm CanonicalResult
call_canonical norm ii rng args = do
  ty <- liftTCM $ do
    metaId <- lookupInteractionId ii
    getMetaTypeInContext metaId
  ctx <- liftTCM $ withInteractionId ii getContextTelescope
  goal <- liftTCM $ (produceCanonicalGoal ctx ty)
  liftIO $
    useAsCString (toStrict (encode goal)) $ \ety -> do -- may be dangerous, have to check
    -- name <- newCString "proof"
    -- res <- canonical ety name 1000 1
    -- fstr <- packCString res
    -- fres :: CTerm <- liftMaybe (decode (fromStrict  fstr))
    return (CanonicalExpr (show goal))
