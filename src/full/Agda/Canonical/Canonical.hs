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
import Agda.Syntax.Common (InteractionId, Arg (unArg, argInfo), Hiding (NotHidden), ArgInfo (argInfoHiding))

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

typeToCDecl :: Type -> -- Type to convert
               [CDecl] ->  -- Pi bindings
               [CDecl] ->  -- lets bindings
               [String] ->  -- Names for variables
               Map String Type -> -- Already seen data types
               Bool -> -- toplevel?
               TCM (CDecl, Map String Type, [CDecl]) -- Converted type along with all datatypes encountered
typeToCDecl t = toCDecl (unEl t)

toCSpine :: Term -> [String] -> [CDecl] -> Map String Type -> TCM (CSpine, Map String Type, [CDecl])
toCSpine t names lts alrdsn =
  case t of
    Var i e -> do
      (args, alrdsn', lts') <-  elimsToCExpr e names lts alrdsn
      return (CSpine {
        head =  names !! i ,
        args
      }, alrdsn', lts')
    Def qname e -> do
      (args, alrdsn', lets') <- elimsToCExpr  e names lts alrdsn
      (lt, ald) <- gatherDatatypeInformations qname lets' alrdsn' names
      return (CSpine {
          head = P.prettyShow (qnameName qname),
          args
        }, ald, lt)
    Con hd _ e -> do
      infos <- getConstInfo (conName hd)
      let (dataname, pars) = case theDef infos of
                    ConstructorDefn cd -> (_conData cd, _conPars cd)
                    _ -> __IMPOSSIBLE__
      (args, alrdsn', lts') <- elimsToCExpr e names lts alrdsn
      (lt, ald) <- gatherDatatypeInformations dataname lts' alrdsn' names
      return (CSpine {
          head = P.prettyShow . qnameName $ conName hd,
          args
        }, ald, lt)
    Sort (Type l) -> do
      t' <- reallyUnLevelView l
      (arg, alrdsn', lts') <- toCExpr t' names lts alrdsn
      return (CSpine {
          head = "Set",
          args = [arg]
        }, alrdsn', lts')
    Sort s ->
      return (CSpine {
          head = P.prettyShow s,
          args = []
        }, alrdsn , lts)
    Level l -> do
      t' <- reallyUnLevelView l
      toCSpine t' names lts alrdsn
    Pi{} -> do
      (cty, alrdsn', lts') <- toCDecl t [] lts names alrdsn False
      return (CSpine {
          head = "(" ++ show cty ++ ")",
          args = []
        }, alrdsn', lts')
    _ -> return (CSpine{
            head  = P.prettyShow t,
            args  = []
      }, alrdsn , lts)

toCDecl  :: Term ->
            [CDecl] ->
            [CDecl] ->
            [String] ->
            Map String Type ->
            Bool -> -- TopLevel ?
            TCM (CDecl, Map String Type, [CDecl])
toCDecl t bds lts names alrdsn tplvl =
  case t of
    Pi a (NoAbs nb b ) -> do
      (domty, alrdsn', lts') <- (typeToCDecl (unDom a) [] lts names alrdsn) False -- (isImplicit a || prms > 0) 0) -- Convert domain type
      typeToCDecl b ((nb , Just domty) : bds) lts' names alrdsn'  tplvl -- implicit (if prms > 0 then (prms  - 1) else 0)-- Convert  codomain type
    Pi a b -> do
      (domty, alrdsn', lts') <- typeToCDecl (unDom a) [] lts names alrdsn False -- (isImplicit a || prms > 0) 0
      typeToCDecl (unAbs b) ((absName b, Just domty) : bds) lts' (absName b : names) alrdsn' tplvl  -- implicit (if prms > 0 then prms - 1 else 0)
    Sort s -> do
      (spine, alrdsns, lets) <- toCSpine t names lts alrdsn -- implicit       -- On defined names
      return (CExpr {
        params = reverse bds,
        lets = if tplvl then reverse lts else [],
        spine
      }, alrdsns, lets)
    Def qname el -> do
      (spine, alrdsns, lets) <- toCSpine t names lts alrdsn -- implicit       -- On defined names
      return (CExpr {
        params = reverse bds,
        lets = if tplvl then reverse lets else [],
        spine
      }, alrdsns, lets )
    _ -> do
      (spine, alrdsns, lets) <- toCSpine t names lts alrdsn  -- implicit    -- On defined names
      return (CExpr {
        params = reverse bds,
        lets = if tplvl then reverse lets else [],
        spine
      }, alrdsns , lets)

elimsToCExpr ::  [Elim' Term] -> [String] ->  [CDecl] -> Map String Type -> TCM ([CExpr], Map String Type, [CDecl])
elimsToCExpr e names lts alrdsn =
  case e of
    [] -> return ([], alrdsn, lts)
    el : els -> do
      (el', alrdsn', lts' ) <- elimToCExpr el names lts alrdsn -- (pars > 0)
      (els', alrdsn'', lts'') <- elimsToCExpr els names lts' alrdsn' -- (pars - 1)
      return (el' : els', alrdsn'' , lts'')
  where

  elimToCExpr  ::  Elim' Term -> [String] ->  [CDecl] -> Map String Type -> TCM (CExpr, Map String Type, [CDecl])
  elimToCExpr c names lts alrdsn = -- pars=
    case c of
      Apply t -> toCExpr (unArg t) names lts alrdsn  -- (pars || argInfoHiding (argInfo t) /= NotHidden)
      e -> return (CExpr {
          params = [],
          lets = [],
          spine = CSpine {
              head = P.prettyShow e,
              args = []
            }
        }, alrdsn, lts)

toCExpr :: Term -> [String] -> [CDecl] -> Map String Type -> TCM (CExpr, Map String Type, [CDecl])
toCExpr t names lts alrdsn = do
  (spine, alrdsn', lets) <- toCSpine t names lts alrdsn
  return (CExpr{
    params = [],
    lets = [],
    spine
  } , alrdsn', lets)

getConstParams :: Definition -> Int
getConstParams d =
  case theDef d of
    ConstructorDefn c -> _conPars c
    _ -> __IMPOSSIBLE__

gatherDatatypeInformations :: QName -> [CDecl] -> Map String Type -> [String] -> TCM ([CDecl], Map String Type)
gatherDatatypeInformations qn lts alrdsn names =
  if ((nameToString  qn) `member` alrdsn) then return (lts, alrdsn)
  else do
    def <- getConstInfo qn                                               -- gather its informations
    let ty = defType def                                                 -- get it's type
    let alrdsn' = insert (nameToString qn) ty alrdsn                                   -- we add the new encoutered type in the list
    (tys, alr, letsss) <- (typeToCDecl ty [] lts names alrdsn' False )   -- convert it and add it to already seen types
    let letss = tys : letsss
    case theDef def of                                                   -- match on the kind of definition we have for the type
      DatatypeDefn DatatypeData { _dataCons = cons } -> do               -- get all the type constructors names
        defs <- mapM getConstInfo cons                                   -- get their informations
        let tys = map (\d -> (defType d, getConstParams d)) defs
        let ald = foldl (\m (k, v) -> insert k v m ) alr (zip (map nameToString  cons) (map fst tys))
        (ctys, alrdsnes, lts'') <- foldlM (\(acc, alrdsn', lets) (t, p) -> do
                                (nt, alrdsns', lets') <- typeToCDecl t [] lets names alrdsn' False -- False p -- (cpt + 1000)
                                return (nt : acc, alrdsns', lets'))
                                ([], ald, letss) tys
        let lteess = (reverse $ ctys) ++ lts''
        return (lteess, alrdsnes)
      _ -> return (letss , alr)

myZip :: [a] -> [b] -> [(a, b, [c])]
myZip [] [] = []
myZip (a : as) (b : bs) = (a, b, []) : myZip as bs
myZip _ _ = __IMPOSSIBLE__

produceCanonicalGoal :: Telescope -> Type -> TCM CDecl
produceCanonicalGoal ctx ty = aux ctx ty [CDecl "Set" Nothing [] ] [] [] mempty
  where

  aux :: Telescope -> Type -> [CDecl] -> [CDecl] -> [String] -> Map String Type ->  TCM CDecl
  aux ctx ty revLets revPis names alrdsn =
    case ctx of
      EmptyTel -> do
        (res , al, _) <- typeToCDecl ty revPis revLets names alrdsn True
        return res
      ExtendTel dom (Abs nb b) ->
        case unEl ty of
          Pi d codom -> do
            (domty, alrdsns, lts') <- (typeToCDecl (unDom dom) [] revLets names alrdsn False)
            aux b (unAbs codom) ((nb, Just domty, []) : lts' ) revPis (nb : names) alrdsns
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
