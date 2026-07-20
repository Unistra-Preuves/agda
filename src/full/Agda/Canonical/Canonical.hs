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
import qualified Generic.Data.Internal.Microsurgery as CExpr
import Agda.Syntax.Concrete.Definitions (NiceConstructor)

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


{-
  Converts a qualified name of Agda into a string.
-}
nameToString :: QName -> String
nameToString = P.prettyShow <$> qnameName

{-
  This function converts an Agda term into a Canonical declaration.
-}

toCDecl :: Term -> -- ^ The term to convert
           String -> -- ^ The name of the declaration
           [String] -> -- ^ already bound names
           [CDecl] -> -- ^ let declarations
           Map String Bool -> -- ^ already seen definitions / constructors
           Bool -> -- ^ is at top level
           TCM (CDecl, [CDecl], Map String Bool)
toCDecl t name bindnames lets ald tplvl = do
  (typ, lets, ald) <- toCExpr t bindnames [] lets ald tplvl
  return $ (CDecl {
        name,
        typ = Just typ,
        equations = []
  }, lets, ald)

{-
  This function converts an Agda term into a Canonical expression.
-}

toCExpr :: Term -> -- ^ The term to convert
           [String] -> -- ^ Bound names
           [CDecl] -> -- ^ Pi declarations
           [CDecl] -> -- ^ Context
           Map String Bool -> -- ^ already seen constructors / definitions
           Bool -> -- ^ is at top level
           TCM (CExpr, [CDecl], Map String Bool)
toCExpr t bindnames pidecl letdecl ald tplvl =
  case t of
    Pi a b -> do
      -- Some Pi terms bind a name in their codomain.
      -- If they do, we have to add the bound name to `bindnames`
      -- for de Bruijn indices to be converted to the right string.
      let newnames = case b of
                      NoAbs _ _ -> bindnames
                      Abs n _ -> n : bindnames
      -- We convert the domain into a CDecl and add it to `pidecl`
      (domdecl, lets, ald) <- toCDecl (unEl $ unDom a) (absName b) bindnames letdecl ald False
      -- Convert the codomain into a Canonical expression
      toCExpr (unEl $ unAbs b) newnames (domdecl : pidecl) lets ald tplvl
    _ -> do
      -- If we are not converting a Pi, we have to convert the term into a spine.
      (spine, lets, ald) <- toCSpine t bindnames letdecl ald
      -- Then we build the Canonical expression by putting together `pidecl`,
      -- `letdecl` and the spine
      return $ (
        CExpr {
            params = reverse pidecl,
            -- We want to add the context only if we are building the top-level CExpr.
            lets = if tplvl then reverse lets else [],
            spine
          }, lets, ald)

{-
  This function converts an Agda term to a Canonical spine.
-}

toCSpine :: Term -> -- ^ The term to convert
            [String] -> -- ^ Bound names
            [CDecl] -> -- ^ Context
            Map String Bool -> -- ^ Already seen constructors / datatypes
            TCM (CSpine, [CDecl], Map String Bool)
toCSpine t bindnames lets ald =
  case t of
    -- On a variable applied to multiple arguments.
    Var i el -> do
      -- We convert the arguments into Canonical expressions.
      (args, lets, ald) <- elimsToCExpr el bindnames lets ald
      return $ (
        CSpine {
          head = bindnames !! i, -- We put the variable at the head of the spine.
          args  -- And put the converted arguments.
         }, lets, ald)
    -- When we encounter a term 'Set l'
    Sort (Type l) -> do
      -- We convert the level into a term
      t' <- reallyUnLevelView l
      -- convert the term into a Canonical expression.
      (arg, lets, ald) <- toCExpr t' bindnames [] lets ald False
      return $ (
        -- Build the spine
        CSpine {
          head = "Set",
          args = [arg]
        }, lets, ald)
    -- On a level alone
    Level l -> do
      -- First convert the level into a term
      t' <- reallyUnLevelView l
      -- Then convert the term into a spine
      toCSpine t' bindnames lets ald

    -- On a datatype name applied to arguments
    Def qname e -> do
      -- We first convert the arguments into Canonical expressions
      (args, lets, ald) <- elimsToCExpr e bindnames lets ald
      -- Then we add all the information related to the datatype to the context.
      (lets, ald) <- gatherDatatypeInformations qname bindnames lets ald
      -- And create the spine
      return $ (
        CSpine {
          head = P.prettyShow (qnameName qname),
          args
        }, lets, ald)

    -- When treating a constructor applied to arguments.
    Con hd _ e -> do
      -- We get its datatype
      infos <- getConstInfo (conName hd)
      let dataname = case theDef infos of
                    ConstructorDefn cd -> _conData cd
                    _ -> __IMPOSSIBLE__
      -- Convert the arguments into Canonical expressions.
      (args, lets, ald) <- elimsToCExpr e bindnames lets ald
      -- Add all the definitions of the datatype.
      (lets, ald) <- gatherDatatypeInformations dataname bindnames lets ald
      -- Build the spine
      return $ (
        CSpine {
          head = P.prettyShow . qnameName $ conName hd,
          args
        }, lets, ald)

    -- Unhandled cases
    e -> return $ (
      CSpine {
        head = P.prettyShow e,
        args = []
      }, lets, ald)

{-
  This function converts a list of Agda eliminators into Canonical expressions.
-}

elimsToCExpr :: [Elim' Term] -> -- ^ The eliminators
                [String] -> -- ^ Bound names
                [CDecl] -> -- ^ Context
                Map String Bool -> -- Already seen datatypes / constructors
                TCM ([CExpr], [CDecl], Map String Bool)
elimsToCExpr e names lets ald =
  case e of
    [] -> return ([], lets, ald)
    el : els -> do
      -- Convert the first argument
      (el, lets, ald) <- elimToCExpr el names lets ald
      -- Convert the rest
      (els, lets, ald) <- elimsToCExpr els names lets ald
      return (el : els, lets, ald)
  where

  elimToCExpr :: Elim' Term -> -- The eliminator
                 [String] -> -- Bound names
                 [CDecl] -> -- Context
                 Map String Bool -> -- Already seen datatypes / constructors
                 TCM (CExpr, [CDecl], Map String Bool)
  elimToCExpr c names lets ald =
    case c of
      -- If it's an application, we just convert the argument into an expression
      Apply t -> toCExpr (unArg t) names [] lets ald False

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
    let ty = defType def
    -- Convert the type
    (ty, lets, ald) <- toCDecl (unEl ty) (nameToString qn) bindnames lets alrd False
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
                                (nt, lets, ald) <- toCDecl t n bindnames lets ald False
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
                        TCM (CDecl, Map String Bool)
produceCanonicalGoal ctx ty =
  -- Add handmade declarations for Cubical
  let decls = [orDecl, andDecl, negDecl, i1Decl, i0Decl, iDecl, setDecl]
      ald = fromList [("i1", True), ("i0", True), ("I", True)]
  in
  aux ctx ty []  decls ald
    where
      {-
        This function unfolds a telescope, converts its elements to declarations, and adds them to the Canonical context.
      -}
      aux :: Telescope -> -- The context telescope
            Type -> -- The type to convert
            [String] -> -- Bound names
            [CDecl] ->  -- Canonical context
            Map String Bool -> -- Already seen datatypes / constructors
            TCM (CDecl, Map String Bool)
      aux ctx ty bindnames lets ald =
        case ctx of
          -- If the telescope is empty, we just have to convert the type
          EmptyTel -> do
            (res, _, ald) <- toCDecl (unEl ty) "Goal" bindnames lets ald True
            return (res, ald)
          -- Otherwise our goal type should be of the form `Pi _ _`
          ExtendTel dom (Abs nb b) ->
            case unEl ty of
              -- We unfold the context
              Pi d codom -> do
                -- Convert the type of the first element of the telescope
                (domdecl, lets, ald) <- toCDecl (unEl $ unDom dom) nb bindnames lets ald False
                -- Convert the rest
                aux b (unAbs codom) (nb : bindnames) (domdecl : lets) ald
              _ -> __IMPOSSIBLE__
          _ -> __IMPOSSIBLE__

{-
  The function called by C-c C-g.
-}

call_canonical :: MonadTCM tcm => Rewrite -> InteractionId -> Range -> String -> tcm CanonicalResult
call_canonical norm ii rng args = do
  -- Get the type of the goal
  ty <- liftTCM $ do
    metaId <- lookupInteractionId ii
    getMetaTypeInContext metaId
  -- Get the context of the goal
  ctx <- liftTCM $ withInteractionId ii getContextTelescope
  -- Produce a goal for Canonical
  (goal, ald) <- liftTCM $ produceCanonicalGoal ctx ty
  -- Add special constructors for Cubical equality in the context (only if equalities appear in the goal type)
  goal' <- case goal of
            CDecl n (Just (CExpr p l s)) e ->
              let nl = if "_≡_" `member` ald then l ++ [mpDecl , dpDecl] else l in
              return $ CDecl n (Just $ CExpr p nl s) e
            _ -> __IMPOSSIBLE__
  liftIO $
    -- Call to Canonical
    useAsCString (toStrict (encode goal')) $ \ety -> do -- may be dangerous, have to check
    cres <- canonical ety 30 1
    cstr <- packCString cres
    results :: [CExpr] <- liftMaybe (decode (fromStrict cstr))
    fres <- case results of
            [] -> return "\nNo solution found."
            (d : _) -> return $ "\n--- Hint :\n" ++ (show d)
    return . CanonicalExpr $ show goal' ++ "\n" ++ fres
