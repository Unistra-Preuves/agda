-- | The left-hand sides of the rewrite rules given by the clauses of a
--   function ('Pat'), and their disjoint instances.
--
--   Agda tries the clauses in order, while Canonical may apply its rewrite
--   rules in any order: each clause only stands for the instances of its
--   patterns that no earlier clause matches ('disjoint').  With @f 1 = 7@
--   and @f (suc n) = n@, the rules are @f 1 ⤇ 7@ and
--   @f (suc (suc y)) ⤇ suc y@.

module Agda.Canonical.ToCanonical.Pattern
  ( -- * Patterns
    Pat(..)
  , isProjPat
  , patExpr
  , patCtors
  , patToPat
  , maxUnaryNat

    -- * Disjoint clauses
  , disjoint
  , clash
  ) where

import Control.Monad (forM, replicateM)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (catMaybes, listToMaybe)

import Agda.Canonical.Types
import Agda.Canonical.Utils
import Agda.Syntax.Builtin
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Literal (Literal (..))
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Signature (HasConstInfo (getConstInfo))
import Agda.Utils.Impossible (__IMPOSSIBLE__)

---------------------------------------------------------------------------
-- * Patterns
---------------------------------------------------------------------------

-- | A pattern of a left-hand side.
--
--   The patterns of a clause may also contain a projection ('LProj'), which
--   is not an argument: see 'Agda.Canonical.ToCanonical.Term.copatSpine'.
data Pat
  = LVar String
      -- ^ A variable, or a wildcard.
  | LCon QName [Pat]
      -- ^ A constructor, applied to the parameters of its datatype
      --   (wildcards) and to its fields.
  | LProj QName
      -- ^ A projection, in a clause by copatterns.

-- | Is it a projection?
isProjPat :: Pat -> Bool
isProjPat LProj{} = True
isProjPat _       = False

-- | A pattern as an argument of a left-hand side, given the names of the
--   constructors.
patExpr :: (QName -> String) -> Pat -> CExpr
patExpr _ (LVar x)     = simpleExpr x
patExpr nm (LCon c ps) = CExpr [] [] (CSpine (nm c) (map (patExpr nm) ps))
patExpr _ LProj{}      = __IMPOSSIBLE__

-- | The constructors of a pattern.
patCtors :: Pat -> [QName]
patCtors (LVar _)    = []
patCtors (LCon c ps) = c : concatMap patCtors ps
patCtors LProj{}     = []

-- | Substitution of patterns for variables in a pattern.
substPat :: Map String Pat -> Pat -> Pat
substPat sub p@(LVar x) = Map.findWithDefault p x sub
substPat sub (LCon c ps) = LCon c (map (substPat sub) ps)
substPat _ p@LProj{} = p

-- | Translates a pattern into a pattern of a left-hand side.
--
--   A dot pattern becomes a fresh wildcard; the parameters of a constructor,
--   absent from Agda patterns, become fresh wildcards; an interval pattern
--   (@f p i = …@) is a variable; a natural number literal is unfolded into
--   @suc (… zero)@; a copattern is an 'LProj'.  The other literals and the
--   other cubical patterns are not supported ('Nothing').
patToPat :: [String] -> DeBruijnPattern -> TCM (Maybe Pat)
patToPat names p = case p of
  LitP _ (LitNat n) | n <= maxUnaryNat -> do
    mz <- getBuiltin' builtinZero
    ms <- getBuiltin' builtinSuc
    return $ case (mz, ms) of
      (Just (Con z _ _), Just (Con s _ _)) ->
        Just (iterate (LCon (conName s) . pure) (LCon (conName z) []) !! fromInteger n)
      _ -> Nothing
  VarP _ x -> return . Just $ LVar (names !! dbPatVarIndex x)
  IApplyP _ _ _ x -> return . Just $ LVar (names !! dbPatVarIndex x)
  DotP _ _ -> Just . LVar <$> freshString "w"
  ProjP _ r -> return . Just $ LProj r
  ConP c _ ps -> do
    np   <- conParCount (conName c)
    ws   <- replicateM np (LVar <$> freshString "p")
    subs <- mapM (patToPat names . namedArg) ps
    return $ LCon (conName c) . (ws ++) <$> sequence subs
  _ -> return Nothing

-- | Number of parameters of the datatype of a constructor.
conParCount :: QName -> TCM Int
conParCount q = do
  d <- getConstInfo q
  return $ case theDef d of
    ConstructorDefn cd -> _conPars cd
    _                  -> __IMPOSSIBLE__

-- | The largest natural number literal unfolded into constructors; the
--   larger ones are opaque constants (see
--   'Agda.Canonical.ToCanonical.Term.literalConst').
maxUnaryNat :: Integer
maxUnaryNat = 1000

---------------------------------------------------------------------------
-- * Disjoint clauses
---------------------------------------------------------------------------

-- | The most instances of a clause with more than this many rules, which
--   is then kept as it is.
maxPieces :: Int
maxPieces = 64

-- | @disjoint ps qss@: the instances of the patterns @ps@ that are not
--   instances of the earlier clauses @qss@, as disjoint lists of patterns,
--   each one with the substitution of the variables of @ps@ that gives it.
--   If there are too many of them ('maxPieces'), the clause is kept as it is.
disjoint :: [Pat] -> [[Pat]] -> TCM [([Pat], Map String Pat)]
disjoint ps0 qss = go [(ps0, Map.empty)] qss
  where
    go acc [] = return acc
    go acc (qs : rest) = do
      acc' <- concat <$> mapM (\ (ps, s) -> map (compose s) <$> minus ps qs) acc
      if length acc' > maxPieces then return [(ps0, Map.empty)] else go acc' rest

-- | @compose s (ps, s')@ applies @s'@ after @s@.
compose :: Map String Pat -> ([Pat], Map String Pat) -> ([Pat], Map String Pat)
compose s (ps, s') = (ps, Map.union (Map.map (substPat s') s) s')

-- | @minus ps qs@: the instances of @ps@ that are not instances of @qs@.  If
--   they clash (different constructors at the same position), all of them;
--   if @qs@ is more general, none; otherwise a variable of @ps@ facing a
--   constructor of @qs@ is replaced by each constructor of its datatype, and
--   so on.
minus :: [Pat] -> [Pat] -> TCM [([Pat], Map String Pat)]
minus ps qs
  | clash ps qs = return [(ps, Map.empty)]
  | otherwise = case firstJust (zipWith splitAt' ps qs) of
      Nothing     -> return []
      Just (x, d) -> do
        cs <- siblingCtors d
        concat <$> forM cs (\ (c, k) -> do
          ys <- replicateM k (LVar <$> freshString "y")
          let s = Map.singleton x (LCon c ys)
          map (compose s) <$> minus (map (substPat s) ps) qs)
  where
    splitAt' (LVar x) (LCon d _)    = Just (x, d)
    splitAt' (LCon _ as) (LCon _ bs) = firstJust (zipWith splitAt' as bs)
    splitAt' _ _                     = Nothing
    firstJust = listToMaybe . catMaybes

-- | Do two lists of patterns differ at a position they both have (different
--   constructors or projections)?
clash :: [Pat] -> [Pat] -> Bool
clash ps qs = or (zipWith differ ps qs)
  where
    differ (LCon c as) (LCon d bs) = c /= d || clash as bs
    differ (LProj r) (LProj s)     = r /= s
    differ _ _                     = False

-- | The constructors of the datatype of a constructor, with their numbers
--   of arguments (parameters included).
siblingCtors :: QName -> TCM [(QName, Int)]
siblingCtors q = do
  d <- theDef <$> getConstInfo q
  cons <- case d of
    ConstructorDefn cd -> theDef <$> getConstInfo (_conData cd) <&> \case
      DatatypeDefn dd -> _dataCons dd
      RecordDefn rd   -> [conName (_recConHead rd)]
      _               -> [q]
    _ -> return [q]
  forM cons $ \ c -> theDef <$> getConstInfo c <&> \case
    ConstructorDefn cd -> (c, _conPars cd + _conArity cd)
    _                  -> __IMPOSSIBLE__
