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
import Agda.Syntax.Common (InteractionId, Arg (unArg))

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
import Agda.Utils.Haskell.Syntax (DataOrNew(DataType))
import Agda.Syntax.Translation.AbstractToConcrete (ToConcrete(toConcrete))
import Agda.TypeChecking.Substitute (Apply(apply), piApply, domFromNamedArgName)
import Data.Foldable (foldlM)
import Data.ByteString.Lazy (fromStrict, toStrict )
import Data.ByteString (packCString, useAsCString)

foreign import ccall "canonical" canonical :: CString -> CString -> Word64 -> Word64 -> IO CString

typeToCType :: Type -> -- Type to convert
               [(String, Maybe CType)] ->  -- Pi bindings
               [(String, Maybe CType)] ->  -- lets bindings
               [String] ->  -- Names for variables
               [String] -> -- Already seen data types
               Bool -> -- toplevel?
               TCM (CType, [String], [(String, Maybe CType)]) -- Converted type along with all datatypes encountered
typeToCType t = toCType (unEl t)

toCSpine :: Term -> [String] -> [(String, Maybe CType)] -> [String] -> TCM (CSpine, [String], [(String, Maybe CType)])
toCSpine t names lts alrdsn =
  case t of
    Var i e -> do
      (sargs, alrdsn', lts') <-  elimsToCterm e names lts alrdsn
      return (CSpine {
        shead =  names !! i ,
        sargs
      }, alrdsn', lts')
    Def qname e -> do
      (sargs, alrdsn', lets') <- elimsToCterm  e names lts alrdsn
      if (((P.prettyShow <$> qnameName ) qname) `elem` alrdsn' ) then do        -- if we already encountered the name,
        return (CSpine {
            shead = P.prettyShow (qnameName qname),
            sargs
          }, alrdsn', lets')
      else do
          def <- getConstInfo qname                                           -- gather its informations
          let ty = defType def                                                -- get it's type
          (tys, alr, letsss) <- (typeToCType ty [] lets' names alrdsn' False)    -- convert it and add it to already seen types
          let letss = (P.prettyShow $ qnameName qname , Just tys) : letsss
          case theDef def of                                                  -- match on the kind of definition we have for the type
            DatatypeDefn DatatypeData { _dataCons = cons } -> do              -- get all the type constructors names
              let alrdsn' = (P.prettyShow <$> qnameName) qname : alr          -- we add the new encoutered type in the list
              defs <- mapM getConstInfo cons                                  -- get their informations
              let tys = map defType defs
              (ctys, alrdsnes, lts'') <- foldlM (\(acc, alrdsn', lets) t -> do
                                      (nt, alrdsns', lets') <- typeToCType t [] lets names alrdsn' False -- (cpt + 1000)
                                      return (nt : acc, alrdsns', lets'))
                                     ([], alrdsn', letss) tys
              let lteess = (reverse $ (zip (map (P.prettyShow <$> qnameName) cons) (map Just (reverse ctys)) ) ) ++ lts''
              return  (CSpine{
                  shead = P.prettyShow (qnameName qname),
                  sargs
                }, alrdsnes, lteess)
            d -> return (CSpine {
                  shead = P.prettyShow (qnameName qname),
                  sargs
              }, alr, letss)

    Con hd _ e -> do
      (sargs, alrdsn', lts') <- elimsToCterm e names lts alrdsn
      return (CSpine {
          shead = P.prettyShow . qnameName $ conName hd,
          sargs
        }, alrdsn', lts')
    _ -> __IMPOSSIBLE__


-- gatherDataTypeInformations :: [String] ->
--                               [(String, Maybe CType)] ->
--                               [String] ->
--                               (TCM (CType, [String], [(String, Maybe CType)]))
-- gatherDataTypeInformations name lts alrdsn =


toCType  :: Term ->
            [(String, Maybe CType)] ->
            [(String, Maybe CType)] ->
            [String] ->
            [String] ->
            Bool -> -- TopLevel ?
            (TCM (CType, [String], [(String, Maybe CType)]))
toCType t bds lts names alrdsn tplvl =
  case t of
    Pi a (NoAbs nb b ) -> do
                (domty, alrdsn', lts') <- (typeToCType (unDom a) [] lts names alrdsn False) -- Convert domain type
                typeToCType b ((nb , Just domty) : bds) lts' names alrdsn'  tplvl -- Convert  codomain type
    Pi a b -> do
      (domty, alrdsn', lts') <- typeToCType (unDom a) [] lts names alrdsn False
      typeToCType (unAbs b) ((absName b, Just domty) : bds) lts' (absName b : names) alrdsn' tplvl
    Sort s -> -- If get a Sort, we just return its name for now
      return (CType {
        bindings = reverse bds,
        lets = if tplvl then reverse lts else [],
        codom = CSpine{
            shead = P.prettyShow s,
            sargs = []
          }
      }, alrdsn, lts)
    Def qname el -> do
      (codom, alrdsns, lets) <- toCSpine t names lts alrdsn       -- On defined names
      return (CType {
        bindings = reverse bds,
        lets = if tplvl then reverse lets else [],
        codom
      }, alrdsns, lets )
    _ -> do
      (codom, alrdsns, lets) <- toCSpine t names lts alrdsn       -- On defined names
      return (CType {
        bindings = reverse bds,
        lets = if tplvl then reverse lets else [],
        codom
      }, alrdsns , lets)

elimsToCterm ::  [Elim' Term] -> [String] ->  [(String, Maybe CType)] -> [String] -> TCM ([CTerm], [String], [(String, Maybe CType)])
elimsToCterm e names lts alrdsn =
  case e of
    [] -> return ([], alrdsn, lts)
    el : els -> do
      (els', alrdsn', lts') <- elimsToCterm els names lts alrdsn
      (el', alrdsn'', lts'' ) <- elimToCterm el names lts' alrdsn'
      return (el' : els', alrdsn'' , lts'')
  where

  elimToCterm  ::  Elim' Term -> [String] ->  [(String, Maybe CType)] -> [String] -> TCM (CTerm, [String], [(String, Maybe CType)])
  elimToCterm c names lts alrdsn =
    case c of
      Apply t -> toCTerm (unArg t) names lts alrdsn
      e -> return (CTerm {
          thead = [],
          targs = CSpine {
              shead = P.prettyShow e,
              sargs = []
            }
        }, alrdsn, lts)

toCTerm :: Term -> [String] -> [(String, Maybe CType)] -> [String] -> TCM (CTerm, [String], [(String, Maybe CType)])
toCTerm t names lts alrdsn = do
  (targs, alrdsn', lets) <- toCSpine t names lts alrdsn
  return (CTerm {
    thead = [],
    targs
  } , alrdsn', lets)

  --   Var x els        ->
  --   Lam ai b         ->
  --   Pi a (NoAbs _ b) ->
  --   Pi a b           ->
  --   Sort s           ->
  --   Level l          ->
  --   MetaV x els      ->
  --   DontCare v       ->
  --   Dummy kind es    ->
  --   Lit l            ->
  --   Def q els        ->
  --   Con c _ci vs     ->

produceCanonicalGoal :: Telescope -> Type -> TCM CType
produceCanonicalGoal ctx ty = aux ctx ty [("Set", Nothing)] [] [] []
  where

  aux :: Telescope -> Type -> [(String, Maybe CType)] -> [(String, Maybe CType)] -> [String] -> [String] ->  TCM CType
  aux ctx ty revLets revPis names alrdsn =
    case ctx of
      EmptyTel -> do
        (res , _, _) <- typeToCType ty revPis revLets names alrdsn True
        return res
      ExtendTel dom (Abs nb b) ->
        case unEl ty of
          Pi _ codom -> do
            (domty, alrdsns, lts') <- (typeToCType (unDom dom) [] revLets names alrdsn False )
            aux b (unAbs codom) ((nb, Just domty) : lts' ) revPis (nb : names) alrdsns
          _ -> return dummyCType -- Is this impossible ?
      _ -> __IMPOSSIBLE__


call_canonical :: MonadTCM tcm => Rewrite -> InteractionId -> Range -> String -> tcm CanonicalResult
call_canonical norm ii rng args = do --withInteractionId ii $ do
  ty <- liftTCM $ do
    metaId <- lookupInteractionId ii
    getMetaTypeInContext metaId
  ctx <- liftTCM $ withInteractionId ii getContextTelescope
  goal <- liftTCM $ (produceCanonicalGoal ctx ty)
  liftIO $
    useAsCString (toStrict (encode goal)) $ \ety -> do -- may be dangerous, have to check
    name <- newCString "proof"
    res <- canonical ety name 1000 1
    fstr <- packCString res
    fres :: CTerm <- liftMaybe (decode (fromStrict  fstr))
    return (CanonicalExpr (show $ show fres))
