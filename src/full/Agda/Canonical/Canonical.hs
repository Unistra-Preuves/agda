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
import Data.Map (Map, member, insert, fromList)
import Text.PrettyPrint (TextDetails(Str))
import Agda.TypeChecking.Level (reallyUnLevelView)
import Data.Vector.Unboxed (DoNotUnboxNormalForm)

foreign import ccall "canonical" canonical :: CString -> Word64 -> Word64 -> IO CString

nameToString :: QName -> String
nameToString = P.prettyShow <$> qnameName

toCDecl :: Term -> -- ^ The term to convert
           String -> -- ^ The name of the declaration
           [String] -> -- ^ already binded names
           [CDecl] -> -- ^ let declarations
           Map String Bool -> -- ^ already seen definitions / constructors
           Bool -> -- ^ is at toplevel
           TCM (CDecl, [CDecl], Map String Bool)
toCDecl t name bindnames lets ald tplvl = do
  (typ, lets, ald) <- toCExpr t bindnames [] lets ald tplvl
  temp <-
    transformEq $ CDecl {
        name,
        typ = Just typ,
        equations = []
  }
  return $ (temp , lets, ald)

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

transformEq :: CDecl -> TCM CDecl
-- transformEq (CDecl n (Just t) []) =
--   case t of
--     CExpr [] lts s ->
--       case s of
--         CSpine "_≡_" [l, CExpr [] [] s, CExpr [] [] lhs, CExpr [] [] rhs] -> do
--           freshi :: Name<- freshName_ ("j" ++ "")
--           return $ CDecl n (Just $ (CExpr ([CDecl (P.prettyShow freshi) (Just $ simpleExpr "I") []]) lts s)) [CEquation (CSpine n [simpleExpr "i0"]) lhs True, CEquation (CSpine n [simpleExpr  "i1"]) rhs True]
--         _ -> return $ CDecl n (Just $ CExpr [] lts s) []
--     _ -> return (CDecl n (Just t) [])

transformEq t = return $ t

produceCanonicalGoal :: Telescope -> Type -> TCM (CDecl, Map String Bool)
produceCanonicalGoal ctx ty =
  let decls = [orDecl, andDecl, negDecl, i1Decl, i0Decl, iDecl, setDecl]
      ald = fromList [("i1", True), ("i0", True), ("I", True)]
  in
  aux ctx ty []  decls ald
  where

  aux :: Telescope ->
         Type ->
         [String] ->
         [CDecl] ->
         Map String Bool ->
         TCM (CDecl, Map String Bool)
  aux ctx ty bindnames lets ald =
    case ctx of
      EmptyTel -> do
        (res, _, ald) <- toCDecl (unEl ty) "Goal" bindnames lets ald True
        return (res, ald)
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
  (goal, ald) <- liftTCM $ produceCanonicalGoal ctx ty
  goal' <- case goal of
            CDecl n (Just (CExpr p l s)) e ->
              let nl = if "_≡_" `member` ald then l ++ [mpDecl] else l in
              return $ CDecl n (Just $ CExpr p nl s) e
            _ -> __IMPOSSIBLE__
  liftIO $
    useAsCString (toStrict (encode goal')) $ \ety -> do -- may be dangerous, have to check
    cres <- canonical ety 30 1
    cstr <- packCString cres
    results :: [CExpr] <- liftMaybe (decode (fromStrict cstr))
    fres <- case results of
            [] -> return "\nNo solution found."
            (d : _) -> return $ "\n--- Hint :\n" ++ (show d)
    return . CanonicalExpr $ show goal' ++ "\n" ++ fres
    -- return . CanonicalExpr $ show goal
