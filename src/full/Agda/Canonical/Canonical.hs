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

typeToCType :: Type -> -- Type to convert
               [(String, Maybe CType)] ->  -- Pi bindings
               [(String, Maybe CType)] ->  -- lets bindings
               [String] ->  -- Names for variables
               Map String Type -> -- Already seen data types
               Bool -> -- toplevel?
               TCM (CType, Map String Type, [(String, Maybe CType)]) -- Converted type along with all datatypes encountered
typeToCType t = toCType (unEl t)

toCSpine :: Term -> [String] -> [(String, Maybe CType)] -> Map String Type -> TCM (CSpine, Map String Type, [(String, Maybe CType)])
toCSpine t names lts alrdsn =
  -- if implicit then do
  --   (arg, alrdsn', lts' ) <- toCTerm t names lts alrdsn -- False
  --   return (CSpine {
  --       shead = ".implicit",
  --       sargs = [arg]
  --     }, alrdsn', lts' )
  -- else
  case t of
    Var i e -> do
      (sargs, alrdsn', lts') <-  elimsToCterm e names lts alrdsn
      return (CSpine {
        shead =  names !! i ,
        sargs
      }, alrdsn', lts')
    Def qname e -> do
      (sargs, alrdsn', lets') <- elimsToCterm  e names lts alrdsn
      (lt, ald) <- gatherDatatypeInformations qname lets' alrdsn' names
      return (CSpine {
          shead = P.prettyShow (qnameName qname),
          sargs
        }, ald, lt)
    Con hd _ e -> do
      infos <- getConstInfo (conName hd)
      let (dataname, pars) = case theDef infos of
                    ConstructorDefn cd -> (_conData cd, _conPars cd)
                    _ -> __IMPOSSIBLE__
      (sargs, alrdsn', lts') <- elimsToCterm e names lts alrdsn
      (lt, ald) <- gatherDatatypeInformations dataname lts' alrdsn' names
      return (CSpine {
          shead = P.prettyShow . qnameName $ conName hd,
          sargs
        }, ald, lt)
    Sort (Type l) -> do
      t' <- reallyUnLevelView l
      (arg, alrdsn', lts') <- toCTerm t' names lts alrdsn
      return (CSpine {
          shead = "Set",
          sargs = [arg]
        }, alrdsn', lts')
    Sort s ->
      return (CSpine {
          shead = P.prettyShow s,
          sargs = []
        }, alrdsn , lts)
    Level l -> do
      t' <- reallyUnLevelView l
      toCSpine t' names lts alrdsn
    Pi{} -> do
      (cty, alrdsn', lts') <- toCType t [] lts names alrdsn False
      return (CSpine {
          shead = "(" ++ show cty ++ ")",   -- parenthésé : un seul argument
          sargs = []
        }, alrdsn', lts')
    _ -> return (CSpine{
            shead  = P.prettyShow t,
            sargs  = []
      }, alrdsn , lts)

isImplicit :: Dom e  -> Bool
isImplicit d = (argInfoHiding $ domInfo d) /= NotHidden

toCType  :: Term ->
            [(String, Maybe CType)] ->
            [(String, Maybe CType)] ->
            [String] ->
            Map String Type ->
            Bool -> -- TopLevel ?
            -- Bool ->
            -- Int -> -- Params nb
            (TCM (CType, Map String Type, [(String, Maybe CType)]))
toCType t bds lts names alrdsn tplvl = -- implicit prms=
  case t of
    Pi a (NoAbs nb b ) -> do
      (domty, alrdsn', lts') <- (typeToCType (unDom a) [] lts names alrdsn) False -- (isImplicit a || prms > 0) 0) -- Convert domain type
      typeToCType b ((nb , Just domty) : bds) lts' names alrdsn'  tplvl -- implicit (if prms > 0 then (prms  - 1) else 0)-- Convert  codomain type
    Pi a b -> do
      (domty, alrdsn', lts') <- typeToCType (unDom a) [] lts names alrdsn False -- (isImplicit a || prms > 0) 0
      typeToCType (unAbs b) ((absName b, Just domty) : bds) lts' (absName b : names) alrdsn' tplvl  -- implicit (if prms > 0 then prms - 1 else 0)
    Sort s -> do -- If get a Sort, we just return its name for now
      (codom, alrdsns, lets) <- toCSpine t names lts alrdsn -- implicit       -- On defined names
      return (CType {
        bindings = reverse bds,
        lets = if tplvl then reverse lts else [],
        codom
      }, alrdsns, lets)
    Def qname el -> do
      (codom, alrdsns, lets) <- toCSpine t names lts alrdsn -- implicit       -- On defined names
      return (CType {
        bindings = reverse bds,
        lets = if tplvl then reverse lets else [],
        codom
      }, alrdsns, lets )
    _ -> do
      (codom, alrdsns, lets) <- toCSpine t names lts alrdsn  -- implicit    -- On defined names
      return (CType {
        bindings = reverse bds,
        lets = if tplvl then reverse lets else [],
        codom
      }, alrdsns , lets)

elimsToCterm ::  [Elim' Term] -> [String] ->  [(String, Maybe CType)] -> Map String Type -> TCM ([CTerm], Map String Type, [(String, Maybe CType)])
elimsToCterm e names lts alrdsn = -- pars =
  case e of
    [] -> return ([], alrdsn, lts)
    el : els -> do
      (el', alrdsn', lts' ) <- elimToCterm el names lts alrdsn -- (pars > 0)
      (els', alrdsn'', lts'') <- elimsToCterm els names lts' alrdsn' -- (pars - 1)
      return (el' : els', alrdsn'' , lts'')
  where

  elimToCterm  ::  Elim' Term -> [String] ->  [(String, Maybe CType)] -> Map String Type -> TCM (CTerm, Map String Type, [(String, Maybe CType)])
  elimToCterm c names lts alrdsn = -- pars=
    case c of
      Apply t -> toCTerm (unArg t) names lts alrdsn  -- (pars || argInfoHiding (argInfo t) /= NotHidden)
      e -> return (CTerm {
          thead = [],
          targs = CSpine {
              shead = P.prettyShow e,
              sargs = []
            }
        }, alrdsn, lts)

toCTerm :: Term -> [String] -> [(String, Maybe CType)] -> Map String Type -> TCM (CTerm, Map String Type, [(String, Maybe CType)])
toCTerm t names lts alrdsn = do -- implicit = do
  (targs, alrdsn', lets) <- toCSpine t names lts alrdsn -- implicit
  return (CTerm {
    thead = [],
    targs
  } , alrdsn', lets)

getConstParams :: Definition -> Int
getConstParams d =
  case theDef d of
    ConstructorDefn c -> _conPars c
    _ -> __IMPOSSIBLE__

gatherDatatypeInformations :: QName -> [(String, Maybe CType)] -> Map String Type -> [String] -> TCM ([(String, Maybe CType)], Map String Type)
gatherDatatypeInformations qn lts alrdsn names =
  if ((nameToString  qn) `member` alrdsn) then return (lts, alrdsn)
  else do
    def <- getConstInfo qn                                               -- gather its informations
    let ty = defType def                                                 -- get it's type
    let alrdsn' = insert (nameToString qn) ty alrdsn                                   -- we add the new encoutered type in the list
    (tys, alr, letsss) <- (typeToCType ty [] lts names alrdsn' False ) --False 0)     -- convert it and add it to already seen types
    let letss = (P.prettyShow $ qnameName qn , Just tys) : letsss
    case theDef def of                                                   -- match on the kind of definition we have for the type
      DatatypeDefn DatatypeData { _dataCons = cons } -> do               -- get all the type constructors names
        defs <- mapM getConstInfo cons                                   -- get their informations
        let tys = map (\d -> (defType d, getConstParams d)) defs
        let ald = foldl (\m (k, v) -> insert k v m ) alr (zip (map nameToString  cons) (map fst tys))
        (ctys, alrdsnes, lts'') <- foldlM (\(acc, alrdsn', lets) (t, p) -> do
                                (nt, alrdsns', lets') <- typeToCType t [] lets names alrdsn' False -- False p -- (cpt + 1000)
                                return (nt : acc, alrdsns', lets'))
                                ([], ald, letss) tys
        let lteess = (reverse $ (zip (map (P.prettyShow <$> qnameName) cons) (map Just (reverse ctys)) ) ) ++ lts''
        -- let ald = foldl (\m (k, v) -> insert k v m ) alrdsnes (zip cons tys)
        return (lteess, alrdsnes)
      _ -> return (letss , alr)
      -- PrimitiveDefn _ -> return (letss, alr)
      -- AxiomDefn _ -> __IMPOSSIBLE__
      -- DataOrRecSigDefn _ -> __IMPOSSIBLE__
      -- GeneralizableVar _ -> __IMPOSSIBLE__
      -- AbstractDefn _ -> __IMPOSSIBLE__
      -- FunctionDefn _ -> __IMPOSSIBLE__
      -- RecordDefn _ -> __IMPOSSIBLE__
      -- ConstructorDefn _ -> __IMPOSSIBLE__
      -- PrimitiveSortDefn _ -> __IMPOSSIBLE__


produceCanonicalGoal :: Telescope -> Type -> TCM (Map String Type, CType)
produceCanonicalGoal ctx ty = aux ctx ty [("Set", Nothing)] [] [] mempty
  where

  aux :: Telescope -> Type -> [(String, Maybe CType)] -> [(String, Maybe CType)] -> [String] -> Map String Type ->  TCM (Map String Type, CType)
  aux ctx ty revLets revPis names alrdsn =
    case ctx of
      EmptyTel -> do
        (res , al, _) <- typeToCType ty revPis revLets names alrdsn True -- False 0
        return (al, res)
      ExtendTel dom (Abs nb b) ->
        case unEl ty of
          Pi d codom -> do
            (domty, alrdsns, lts') <- (typeToCType (unDom dom) [] revLets names alrdsn False) -- (isImplicit d)) 0
            aux b (unAbs codom) ((nb, Just domty) : lts' ) revPis (nb : names) alrdsns
          _ -> __IMPOSSIBLE__ -- Is this impossible ?
      _ -> __IMPOSSIBLE__

call_canonical :: MonadTCM tcm => Rewrite -> InteractionId -> Range -> String -> tcm CanonicalResult
call_canonical norm ii rng args = do
  ty <- liftTCM $ do
    metaId <- lookupInteractionId ii
    getMetaTypeInContext metaId
  ctx <- liftTCM $ withInteractionId ii getContextTelescope
  (al, goal) <- liftTCM $ (produceCanonicalGoal ctx ty)
  liftIO $
    useAsCString (toStrict (encode goal)) $ \ety -> do -- may be dangerous, have to check
    -- name <- newCString "proof"
    -- res <- canonical ety name 1000 1
    -- fstr <- packCString res
    -- fres :: CTerm <- liftMaybe (decode (fromStrict  fstr))
    return (CanonicalExpr (show $ goal))
