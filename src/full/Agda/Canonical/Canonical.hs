-- | Proof search with Canonical (@C-c C-g@).
--
--   The goal is translated by "Agda.Canonical.ToCanonical", solved by
--   Canonical through "Agda.Canonical.FFI", and the solutions are printed in
--   Agda syntax by "Agda.Canonical.FromCanonical".  The options written in
--   the hole are described in "Agda.Canonical.Options".

module Agda.Canonical.Canonical
  ( callCanonical
  ) where

import Control.Monad (forM)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.IntMap qualified as IntMap
import Data.Map qualified as Map

import Agda.Canonical.FFI (runCanonical)
import Agda.Canonical.FromCanonical (cexprToAgda)
import Agda.Canonical.Options
import Agda.Canonical.ToCanonical (produceCanonicalGoal)
import Agda.Canonical.Types
import Agda.Canonical.Utils (nameToString)
import Agda.Interaction.Base (Rewrite)
import Agda.Interaction.BasicOps (parseExprIn)
import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Common (InteractionId)
import Agda.Syntax.Internal
import Agda.Syntax.Position (Range)
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Context (getContextArgs, getContextTelescope)
import Agda.TypeChecking.Monad.MetaVars
import Agda.TypeChecking.Substitute

-- | Runs Canonical on a goal.
--
--   The output shows the problem sent to Canonical, followed by the solutions.
callCanonical
  :: MonadTCM tcm
  => Rewrite        -- ^ Normalisation level (currently unused).
  -> InteractionId  -- ^ The goal.
  -> Range          -- ^ Its range.
  -> String         -- ^ Its content: the options.
  -> tcm CanonicalResult
callCanonical _norm ii rng s =
  case parseCanonicalOptions s of
    Left err   -> return . CanonicalExpr $ "Canonical: " ++ err ++ "\n" ++ canonicalUsage
    Right opts -> do
      -- An unknown name raises the usual scope error.
      lemmas <- liftTCM $ forM (optLemmas opts) $ \ l ->
        (,) l . lemmaName <$> parseExprIn ii rng l
      case [ l | (l, Nothing) <- lemmas ] of
        []  -> solve ii opts [ q | (_, Just q) <- lemmas ]
        bad -> return . CanonicalExpr $
          "Canonical: these lemmas are not names of definitions: " ++ unwords bad

-- | The definition named by a lemma: a function, a postulate, a datatype,
--   a constructor or a projection.
lemmaName :: A.Expr -> Maybe QName
lemmaName e = case e of
  A.ScopedExpr _ e' -> lemmaName e'
  A.Def' q _        -> Just q
  A.Con c           -> Just (A.headAmbQ c)
  A.Proj _ p        -> Just (A.headAmbQ p)
  _                 -> Nothing

-- | Translates the goal, calls Canonical, and prints the solutions.
solve :: MonadTCM tcm => InteractionId -> CanonicalOptions -> [QName] -> tcm CanonicalResult
solve ii opts lemmas = do
  -- Cubical boundary of the goal (not used by the translation yet).
  bds <- liftTCM . withInteractionId ii $ do
    ip <- lookupInteractionPoint ii
    as <- getContextArgs
    let go (im, r) = do
          eqns <- forM (IntMap.toList im) $ \ (a, b) -> return (Var a [], b)
          return (eqns, r `apply` as)
    traverse go (Map.toList . getBoundary $ ipBoundary ip)
  ty  <- liftTCM $ getMetaTypeInContext =<< lookupInteractionId ii
  ctx <- liftTCM $ withInteractionId ii getContextTelescope
  -- Name of the function containing the hole, for the recursive calls.
  self <- liftTCM $ do
    ip <- lookupInteractionPoint ii
    return $ case ipClause ip of
      IPClause { ipcQName = q } -> nameToString q
      IPNoClause                -> "rec"
  (goal, info) <- liftTCM $ produceCanonicalGoal lemmas ctx ty bds
  results <- liftIO $ runCanonical goal (optTimeout opts) (optCount opts)
  let pp   = cexprToAgda info (maybe [] lets (typ goal)) self
      sols = case results of
        []  -> "No solution found."
        [d] -> "--- Hint :\n" ++ pp d
        ds  -> "--- Hints :\n" ++ unlines [ show i ++ ". " ++ pp d | (i, d) <- zip [1 :: Int ..] ds ]
  return . CanonicalExpr $ show goal ++ "\n\n" ++ sols
