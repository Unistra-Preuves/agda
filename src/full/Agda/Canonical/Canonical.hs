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

toCSpine :: Term -> [String] -> TCM CSpine
toCSpine t names =
  case t of
    Var i e -> do
      sargs <-  mapM (elimsToCterm names) e
      return CSpine {
        shead =  names !! i ,
        sargs
      }
    Def qname e -> do
      sargs <- mapM (elimsToCterm names) e
      return CSpine {
          shead = P.prettyShow $ qnameName qname,
          sargs
        }
    Con hd _ e -> do
      sargs  <- mapM (elimsToCterm names) e
      return CSpine {
          shead = P.prettyShow . qnameName $ conName hd,
          sargs
        }
    _ -> __IMPOSSIBLE__


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
      codom <- toCSpine t names       -- On defined names
      if (((P.prettyShow <$> qnameName ) qname) `elem` alrdsn ) then -- if we already encountered the name,
         return (CType {                                                         -- we already have gathered all its informations and put them in lts
            bindings  = reverse bds,                                             -- we just give the type by its name
            lets = if tplvl then reverse lts else [],
            codom
          }, alrdsn, lts)
      else do
          def <- getConstInfo qname                                           -- gather its informations
          let ty = defType def                                                -- get it's type
          (tys, alr, letsss) <- (typeToCType ty [] lts names alrdsn False)    -- convert it and add it to already seen types
          let letss = (P.prettyShow $ qnameName qname , Just tys) : letsss
          case theDef def of                                                  -- match on the kind of definition we have for the type
            DatatypeDefn DatatypeData { _dataCons = cons } -> do              -- get all the type constructors names
              let alrdsn' = (P.prettyShow <$> qnameName) qname : alr            -- we add the new encoutered type in the list
              defs <- mapM getConstInfo cons                                  -- get their informations
              let tys = map defType defs
              (ctys, alrdsnes, lts'') <- foldlM (\(acc, alrdsn', lets) t -> do
                                      (nt, alrdsns', lets') <- typeToCType t [] lets names alrdsn' False -- (cpt + 1000)
                                      return (nt : acc, alrdsns', lets'))
                                     ([], alrdsn', letss) tys
              let lteess = (reverse $ (zip (map (P.prettyShow <$> qnameName) cons) (map Just (reverse ctys)) ) ) ++ lts''
              return  (CType {
                  bindings  = reverse bds,
                  lets = if tplvl then reverse lteess else [],
                  codom
                }, alrdsnes, lteess)
            d -> return (CType {
                bindings = reverse bds,
                lets = if tplvl then reverse letss else [],
                codom
              }, alr, letss)
    _ -> do
      codom <- toCSpine t names
      return (CType {
        bindings = reverse bds,
        lets = if tplvl then reverse lts else [],
        codom
      }, alrdsn , lts)


-- myZip :: [String] -> [Maybe CType] -> [(String, Maybe CType)]
-- myZip [] [] = []
-- myZip (s : ss) (t : tt) = (s , t) : (myZip ss tt)
-- myZip [] (_ : _) = __IMPOSSIBLE__
-- myZip (_ : _) [] = __IMPOSSIBLE__


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
toCTerm t names = do
  targs <- toCSpine t names
  return CTerm {
    thead = [],
    targs
  }
  -- case t of
  --   Var _ _ -> do
  --     targs <- toCSpine t names
  --     return CTerm {
  --         thead = [],
  --         targs
  --     }
  --
  --   _ -> return dummyCTerm

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
    return (CanonicalExpr (show fres))
