-- | Induction hypotheses of a goal.
--
--   When the hole is in a clause whose left-hand side matches constructors,
--   say @f (suc n) (suc m) = ?@, the variables bound under them (@n@, @m@)
--   are structurally smaller than the arguments of the clause.  The
--   recursive calls on such variables that Agda's termination checker
--   accepts are given to Canonical as hypotheses of the context:
--   @f n (suc m)@, @f (suc n) m@, @f n m@, @f m n@, …
--
--   A call replaces some explicit arguments of the clause by smaller
--   variables, and keeps the others.  If that call is ill-typed (e.g.
--   @f (suc n) xs@ for @f : (n : ℕ) → Vec A n → …@), the implicit and dot
--   arguments, then all the arguments that are not variables, are inferred
--   by unification instead (@f n xs@).  Calls that remain ill-typed, whose
--   arguments cannot be inferred, or that may not terminate, are dropped.
--
--   Termination is checked as by Agda's termination checker, for this call
--   alone: the call matrix relates each new argument to the arguments of the
--   clause (smaller, equal or unknown), and every idempotent matrix of its
--   closure under composition must decrease on its diagonal.  Agda checks
--   the calls actually written again when the file is reloaded.

module Agda.Canonical.Induction
  ( inductionHypotheses
  ) where

import Control.Monad (replicateM)
import Control.Monad.Except (catchError)
import Data.List (nub, nubBy, transpose)
import Data.Maybe (catMaybes, listToMaybe)

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.MetaVars (noMetas)
import Agda.Syntax.Internal.Pattern (patternsToElims)
import Agda.TypeChecking.CheckInternal (infer)
import Agda.TypeChecking.Constraints (noConstraints)
import Agda.TypeChecking.MetaVars (newValueMeta)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce (instantiateFull, reduce)
import Agda.TypeChecking.Substitute
import Agda.Utils.List ((!!!))
import Agda.Utils.Size (size)

-- | At most this many calls are tried.
maxCandidates :: Int
maxCandidates = 64

-- | The induction hypotheses of a goal, as terms with their types, in the
--   context of the goal.
inductionHypotheses :: InteractionId -> TCM [(Term, Type)]
inductionHypotheses ii = do
  ip <- lookupInteractionPoint ii
  case ipClause ip of
    IPNoClause -> return []
    IPClause { ipcQName = f, ipcClauseNo = i } -> (`catchError` \ _ -> return []) $ do
      def <- getConstInfo f
      case theDef def of
        Function { funClauses = cs } | Just cl <- cs !!! i -> withInteractionId ii $ do
          -- The context of the goal extends the telescope of the clause
          -- with the binders of the right-hand side (e.g. λs).
          k <- subtract (size (clauseTel cl)) <$> getContextSize
          let ps = raise k (namedClausePats cl)
              es = patternsToElims ps
          case mapM isApply es of
            Just as | k >= 0 -> do
              hs <- catMaybes <$> mapM (hypothesis f (defType def) ps as) (candidates ps)
              -- The same call may come from several candidates.
              return (nubBy (\ a b -> fst a == fst b) hs)
            _ -> return []   -- copatterns are not supported
        _ -> return []
  where
    isApply (Apply a) = Just a
    isApply _         = Nothing

-- | The variables of a pattern.
patVars :: DeBruijnPattern -> [Int]
patVars p = case p of
  VarP _ x     -> [dbPatVarIndex x]
  ConP _ _ sub -> concatMap (patVars . namedArg) sub
  _            -> []

-- | The variables bound strictly under a constructor of a pattern.
smallerVars :: DeBruijnPattern -> [Int]
smallerVars p = case p of
  ConP _ _ sub -> concatMap (patVars . namedArg) sub
  _            -> []

-- | The calls to try: for each explicit argument, either the argument of the
--   clause ('Nothing') or a smaller variable.  At least one argument is
--   replaced; the calls replacing fewer arguments come first.
candidates :: [NamedArg DeBruijnPattern] -> [[Maybe Int]]
candidates ps = take maxCandidates
  [ [ lookup j (zip js vs) | j <- [0 .. length ps - 1] ]
  | r  <- [1 .. length vis]
  , js <- subsets r vis
  , vs <- replicateM r xs ]
  where
    xs  = nub (concatMap (smallerVars . namedArg) ps)
    vis = [ j | (j, p) <- zip [0 ..] ps, visible p ]
    subsets :: Int -> [Int] -> [[Int]]
    subsets 0 _        = [[]]
    subsets _ []       = []
    subsets r (y : ys) = map (y :) (subsets (r - 1) ys) ++ subsets r ys

-- | The recursive call of @f@ (of type @fty@) replacing the arguments @as@
--   of the clause (with patterns @ps@) as chosen: 'Nothing' if it is
--   ill-typed or may not terminate.
hypothesis :: QName -> Type -> [NamedArg DeBruijnPattern] -> [Arg Term] -> [Maybe Int]
           -> TCM (Maybe (Term, Type))
hypothesis f fty ps as choice =
  listToMaybe . catMaybes <$> mapM attempt
    [ const False
    , \ p -> not (visible p) || isDot (namedArg p)
    , \ p -> not (isVar (namedArg p))
    ]
  where
    isDot DotP{} = True
    isDot _      = False
    isVar VarP{} = True
    isVar _      = False

    -- Builds the call, the kept arguments selected by @meta@ being inferred.
    -- The metas are discarded with the state: the result has none left.
    attempt meta = (`catchError` \ _ -> return Nothing) $ localTCState $ do
      mes <- args meta fty (zip3 ps as choice)
      case mes of
        Nothing -> return Nothing
        Just es -> do
          t  <- noConstraints (infer (Def f es))
          v' <- instantiateFull (Def f es)
          t' <- instantiateFull t
          return $ case v' of
            Def _ es' | noMetas v', noMetas t'
                      , Just new <- mapM isApply es'
                      , terminates (callMatrix ps (map unArg as) (map unArg new))
                      -> Just (v', t')
            _ -> Nothing

    args _ _ [] = return (Just [])
    args meta ty ((p, a, c) : rest) = do
      ty' <- reduce ty
      case unEl ty' of
        Pi dom b -> do
          u <- case c of
            Just x               -> return (Var x [])
            Nothing | meta p     -> snd <$> newValueMeta RunMetaOccursCheck CmpLeq (unDom dom)
                    | otherwise  -> return (unArg a)
          fmap (Apply (u <$ a) :) <$> args meta (absApp b u) rest
        _ -> return Nothing

    isApply (Apply a) = Just a
    isApply _         = Nothing

---------------------------------------------------------------------------
-- * Termination
---------------------------------------------------------------------------

-- | How a new argument relates to an argument of the clause.
--   The constructors are ordered from the most to the least informative.
data Order = Lt | Le | Unknown
  deriving (Eq, Ord)

-- | Composition of two relations in sequence.
seqOrder :: Order -> Order -> Order
seqOrder Lt Lt = Lt
seqOrder Lt Le = Lt
seqOrder Le Lt = Lt
seqOrder Le Le = Le
seqOrder _  _  = Unknown

-- | A call matrix: the entry @(i, k)@ relates the new argument @i@ to the
--   argument @k@ of the clause.
type Matrix = [[Order]]

-- | The call matrix of a recursive call.
callMatrix :: [NamedArg DeBruijnPattern] -> [Term] -> [Term] -> Matrix
callMatrix ps old new =
  [ [ order v p o | (p, o) <- zip ps old ] | v <- new ]
  where
    order v p o
      | Var x [] <- v, x `elem` smallerVars (namedArg p) = Lt
      | v == o                                          = Le
      | otherwise                                       = Unknown

-- | Composition of call matrices: first @a@, then @b@.
compose :: Matrix -> Matrix -> Matrix
compose b a =
  [ [ minimum (Unknown : zipWith seqOrder row col) | col <- transpose a ] | row <- b ]

-- | Does the call terminate, when it is the only recursive call?
terminates :: Matrix -> Bool
terminates m = all decreasing (closure [m])
  where
    decreasing c = compose c c /= c || Lt `elem` zipWith (!!) c [0 ..]
    closure s
      | null new || length s > 256 = s
      | otherwise                  = closure (s ++ new)
      where new = nub [ c | a <- s, b <- s, let c = compose a b, c `notElem` s ]
