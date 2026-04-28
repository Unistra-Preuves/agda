{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Agda.Canonical.Canonical where


import Data.Aeson
import Data.Maybe
import Data.String (IsString (fromString))
import Data.Word
import Foreign.C (CString, newCString, peekCString)
import GHC.Generics (Generic, C1)
-- import qualified Agda.Compiler.Backend as Agda.Canonical
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
import Agda.Utils.Impossible (impossible)

foreign import ccall "canonical" canonical :: CString -> CString -> Word64 -> Word64 -> IO CString

dummyCSpine :: CSpine
dummyCSpine = CSpine {
    shead = "",
    sargs = []
  }

dummyCTerm :: CTerm
dummyCTerm = CTerm {
    thead = [],
    targs = dummyCSpine
  }

dummyCType :: CType
dummyCType = CType {
    bindings = [],
    lets = [],
    codom = dummyCSpine
  }

typeToCType :: Type -> [(String, Maybe CType)] -> [(String, Maybe CType)]-> [String] -> CType
typeToCType t binds lts names = toCType (unEl t) binds lts names

toCSpine :: Term -> [String] -> CSpine
toCSpine t names =
  case t of
    Var i e -> CSpine {
        shead =  names !! i ,
        sargs = map (\z -> elimsToCterm z names) e
      }
    _ -> dummyCSpine


toCType  :: Term -> [(String, Maybe CType)] -> [(String, Maybe CType)]-> [String]-> CType
toCType t bds lts names =
  case t of
    Pi a (NoAbs nb b ) -> typeToCType
                b
                ((nb , Just (typeToCType (unDom a) [] [] names)) : bds)
                lts
                names
    Pi a b -> typeToCType
                (unAbs b)
                ((absName b, Just (typeToCType (unDom a) [] [] names)) : bds)
                lts
                (absName b : names)
    Sort s -> CType {
        bindings = [],
        lets = [],
        codom = CSpine{
            shead = P.prettyShow s,
            sargs = []
          }
      }
    _ -> CType {
        bindings = reverse bds,
        lets = reverse lts,
        codom = toCSpine t names
      }


elimsToCterm :: Elim' Term -> [String] -> CTerm
elimsToCterm c names =
  case c of
    Apply t -> toCTerm (unArg t) names
    _ -> dummyCTerm

toCTerm :: Term -> [String] -> CTerm
toCTerm t names =
  case t of
    Var _ _ -> CTerm {
        thead = [],
        targs = toCSpine t names
      }
    _ -> dummyCTerm

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

produceCanonicalGoal :: Telescope -> Type -> CType
produceCanonicalGoal ctx ty = aux ctx ty [("Set", Nothing)] [] []
  where

  aux :: Telescope -> Type -> [(String, Maybe CType)] -> [(String, Maybe CType)] -> [String] -> CType
  aux ctx ty revLets revPis names =
    case ctx of
      EmptyTel -> typeToCType ty revPis revLets names
      ExtendTel dom (Abs nb b) ->
        case unEl ty of
          Pi _ codom -> aux b (unAbs codom) ((nb, Just (typeToCType (unDom dom) [] [] names)) : revLets ) revPis (nb : names)
          _ -> dummyCType -- Is this impossible ?
      _ -> dummyCType  -- This case is impossible, future refactoring to produce proper haskell code


call_canonical :: MonadTCM tcm => Rewrite -> InteractionId -> Range -> String -> tcm CanonicalResult
call_canonical norm ii rng args = do --withInteractionId ii $ do
  ty <- liftTCM $ do
    metaId <- lookupInteractionId ii
    getMetaTypeInContext metaId
  ctx <- liftTCM $ withInteractionId ii getContextTelescope
  liftIO $ do
    ety <- newCString  ("debug : " ++ show (produceCanonicalGoal ctx ty) )--  ("ctx : " ++ show ctx ++ "\nty :" ++ P.prettyShow ty) -- (typeToCType target [] [] []))
    name <- newCString "proof"
    res <- canonical ety name 1000 1
    fstr <- peekCString res
    return (CanonicalExpr fstr)



-- main :: IO ()
-- main = do
--   cstr <- newCString (show $ encode ty)
--   name <- newCString "proof"
--   res <- canonical cstr name 1000 1
--   fstr <- peekCString res
--   print (fromMaybe (Term {thead = [], targs = Spine {shead = "Error", sargs = []}}) (decode (fromString fstr)))
