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

foreign import ccall "canonical" canonical :: CString -> CString -> Word64 -> Word64 -> IO CString

typeToCType :: Type -> -- Type to convert
               [(String, Maybe CType)] ->  -- Pi bindings
               [(String, Maybe CType)] ->  -- lets bindings
               [String] ->  -- Names for variables
               [QName] -> -- Already seen data types
               Bool -> -- toplevel?
               TCM (CType, [QName], [(String, Maybe CType)]) -- Converted type along with all datatypes encountered
typeToCType t = toCType (unEl t)

toCSpine :: Term -> [String] -> TCM CSpine
toCSpine t names =
  case t of
    Var i e -> do
      sargs <-  mapM (elimsToCterm names) e
      return CSpine {
        shead =  names !! i ,
        sargs
      }

    _ -> __IMPOSSIBLE__


toCType  :: Term ->
            [(String, Maybe CType)] ->
            [(String, Maybe CType)] ->
            [String] ->
            [QName] ->
            Bool -> -- TopLevel ?
            TCM (CType, [QName], [(String, Maybe CType)])
toCType t bds lts names alrdsn tplvl =
  case t of
    Pi a (NoAbs nb b ) -> do
                (domty, alrdsn, lts) <- (typeToCType (unDom a) [] lts names alrdsn False)
                typeToCType b ((nb , Just domty) : bds) lts names alrdsn  tplvl
    Pi a b -> do
      (domty, alrdsn, lts) <- typeToCType (unDom a) [] lts names alrdsn False
      typeToCType (unAbs b) ((absName b, Just domty) : bds) lts (absName b : names) alrdsn tplvl
    Sort s ->
      return (CType {
        bindings = reverse bds,
        lets = if tplvl then reverse lts else [],
        codom = CSpine{
            shead = P.prettyShow s,
            sargs = []
          }
      }, alrdsn, lts)
    Def qname el ->
      if (qname `elem` alrdsn ) then
         return (CType {
            bindings  = reverse bds,
            lets = if tplvl then reverse lts else [],
            codom = CSpine {
                shead = P.prettyShow (qnameName qname),
                sargs = []
              }
          }, alrdsn, lts)
      else do
          def <- getConstInfo qname
          let ty = defType def -- Oublie pas de l'ajouter ça serait dommage
          case theDef def of
            DatatypeDefn DatatypeData { _dataCons = cons } -> do
              defs <- mapM getConstInfo cons
              let tys = map defType defs
              (ctys, alrdsn, lts) <- foldlM (\(acc, alrdsn, lts) t -> do
                                      (nt, alrdsn, lts) <- typeToCType t [] lts names alrdsn False
                                      return (nt : acc, alrdsn, lts))
                                     ([], qname : alrdsn, lts) tys
              let lts = (zip (map (P.prettyShow <$> qnameName) cons) (map Just ctys) ) ++ lts
              return  (CType {
                  bindings  = reverse bds,
                  lets = if tplvl then reverse lts else [],
                  codom = CSpine {
                      shead = P.prettyShow (qnameName  qname),
                      sargs = []
                    }
                }, qname : alrdsn, lts)
            d -> return (CType {
                bindings = reverse bds,
                lets = if tplvl then reverse lts else [],
                codom  = CSpine {
                    shead  = P.prettyShow d,
                    sargs  = []
                  }
              }, qname : alrdsn, lts)
    _ -> do
      codom <- toCSpine t names
      return (CType {
        bindings = reverse bds,
        lets = if tplvl then reverse lts else [],
        codom
      }, alrdsn , lts)


elimsToCterm :: [String] -> Elim' Term -> TCM CTerm
elimsToCterm names c =
  case c of
    Apply t -> toCTerm (unArg t) names
    e -> return CTerm {
        thead = [],
        targs = CSpine {
            shead = P.prettyShow e,
            sargs = []
          }
      }

toCTerm :: Term -> [String] -> TCM CTerm
toCTerm t names =
  case t of
    Var _ _ -> do
      targs <- toCSpine t names
      return CTerm {
          thead = [],
          targs
      }
    _ -> return dummyCTerm

      -- Var x els ->
      -- Lam ai b   ->
      -- Pi a (NoAbs _ b)     ->
      -- Pi a b               ->
--       Sort s      ->
--       Level l     ->
--       MetaV x els ->
--       DontCare v  ->
--       Dummy kind es ->
--       Lit l                ->
--       Def q els            ->
--       Con c _ci vs         ->
--

produceCanonicalGoal :: Telescope -> Type -> TCM CType
produceCanonicalGoal ctx ty = aux ctx ty [("Set", Nothing)] [] [] []
  where

  aux :: Telescope -> Type -> [(String, Maybe CType)] -> [(String, Maybe CType)] -> [String] -> [QName] ->  TCM CType
  aux ctx ty revLets revPis names alrdsn =
    case ctx of
      EmptyTel -> do
        (res , _, _) <- typeToCType ty revPis revLets names alrdsn True
        return res
      ExtendTel dom (Abs nb b) ->
        case unEl ty of
          Pi _ codom -> do
            (domty, alrdsn, lts) <- (typeToCType (unDom dom) [] revLets names alrdsn False)
            aux b (unAbs codom) ((nb, Just domty) : lts ) revPis (nb : names) alrdsn
          _ -> return dummyCType -- Is this impossible ?
      _ -> __IMPOSSIBLE__


call_canonical :: MonadTCM tcm => Rewrite -> InteractionId -> Range -> String -> tcm CanonicalResult
call_canonical norm ii rng args = do --withInteractionId ii $ do
  ty <- liftTCM $ do
    metaId <- lookupInteractionId ii
    getMetaTypeInContext metaId
  ctx <- liftTCM $ withInteractionId ii getContextTelescope
  goal <- liftTCM $ (produceCanonicalGoal ctx ty)
  liftIO $ do
    ety <- newCString (show $ encode goal) --
    name <- newCString "proof"
    res <- canonical ety name 1000 1
    fstr <- peekCString res
    fres :: CTerm <- liftMaybe (decode (fromString  fstr))
    return (CanonicalExpr (show fres))
