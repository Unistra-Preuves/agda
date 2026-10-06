-- | Fresh names and η-expansion of Canonical expressions.
--
--   Canonical expects terms in η-long form: a symbol of arity @n@ is always
--   applied to @n@ arguments, and a variable of function type is written
--   @λ z₁ … zₙ. x z₁ … zₙ@.

module Agda.Canonical.Utils
  ( freshString
  , nameToString
  , metaVarName
  , etaVar
  , etaExtend
  , etaTo
  ) where

import Control.Monad (replicateM)

import Agda.Canonical.Types
import Agda.Syntax.Common (MetaId(..), NameId(..))
import Agda.Syntax.Common.Pretty qualified as P
import Agda.Syntax.Internal (QName, qnameName)
import Agda.TypeChecking.Monad.Base (MonadFresh(..), TCM)

-- | @freshString s@ is @s.n@ for a fresh @n@.
--
--   The suffix is removed when printing back to Agda
--   (see "Agda.Canonical.FromCanonical").
freshString :: MonadFresh NameId m => String -> m String
freshString s = do
  NameId n _ <- fresh
  return (s ++ "." ++ show n)

-- | The unqualified name of a definition, as declared to Canonical.
nameToString :: QName -> String
nameToString = P.prettyShow . qnameName

-- | The variable standing for a meta of the goal
--   (see "Agda.Canonical.ToCanonical", goals with metas).
metaVarName :: MetaId -> String
metaVarName m = "?" ++ show (metaId m)

-- | @etaVar x k@ is the η-long form @λ z₁ … z_k. x z₁ … z_k@ of a variable of arity @k@.
etaVar :: String -> Int -> TCM CExpr
etaVar x k = do
  zs <- replicateM k (freshString "z")
  return $ CExpr (map (\ z -> CDecl z Nothing []) zs) [] (CSpine x (map simpleExpr zs))

-- | @etaExtend j e@ adds @j@ fresh binders to @e@ and applies its head to them.
etaExtend :: Int -> CExpr -> TCM CExpr
etaExtend j (CExpr ps ls (CSpine h as)) = do
  xs <- replicateM j (freshString "x")
  return $ CExpr (ps ++ map (\ x -> CDecl x Nothing []) xs) ls
                 (CSpine h (as ++ map simpleExpr xs))

-- | @etaTo k e@ η-expands @e@ until it has at least @k@ binders.
etaTo :: Int -> CExpr -> TCM CExpr
etaTo k ce
  | m < k     = etaExtend (k - m) ce
  | otherwise = return ce
  where m = length (params ce)
