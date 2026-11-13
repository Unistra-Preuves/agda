-- | Tests for "Agda.Canonical.Types".

module Internal.Canonical.Types ( tests ) where

import Data.Map (Map)
import Data.Map qualified as Map

import Agda.Canonical.Types

import Internal.Helpers

------------------------------------------------------------------------
-- * Generators
------------------------------------------------------------------------

-- | The variables that are substituted.  They are never bound.
substituted :: [String]
substituted = ["a", "b", "c"]

-- | The names of the binders of the generated expressions, fresh with
--   respect to the substituted variables and to the free variables of the
--   values, as the names of the translation are.
binders :: [String]
binders = ["x", "y", "z"]

-- | The other symbols.
constants :: [String]
constants = ["f", "g", "Type"]

-- | An expression over the substituted variables, the binders and the
--   constants.
newtype Expr = Expr CExpr

instance Show Expr where
  show (Expr e) = show e

instance Arbitrary Expr where
  arbitrary = Expr <$> sized expr

-- | An expression of the given size.
expr :: Int -> Gen CExpr
expr n = do
  k  <- choose (0, min 2 n)
  ps <- vectorOf k (decl (n `div` 2))
  CExpr ps [] <$> spineOf (n `div` 2) (map name ps)

-- | A binder, with a type or not.
decl :: Int -> Gen CDecl
decl n = do
  x  <- elements binders
  ty <- frequency [(1, pure Nothing), (2, Just <$> expr (n `div` 2))]
  return (CDecl x ty [])

-- | A spine whose head is a substituted variable, a constant or one of the
--   given bound names.
spineOf :: Int -> [String] -> Gen CSpine
spineOf n bound = do
  h  <- elements (substituted ++ constants ++ bound)
  k  <- choose (0, min 2 n)
  as <- vectorOf k (expr (n `div` 2))
  return (CSpine h as)

-- | A first-order substitution: each substituted variable is given a
--   constant applied to arguments without binders.
newtype FirstOrder = FirstOrder (Map String CExpr)

instance Show FirstOrder where
  show (FirstOrder s) = show (Map.toList s)

instance Arbitrary FirstOrder where
  arbitrary = FirstOrder . Map.fromList <$> pickSome substituted
    where
      pickSome xs = fmap concat $ mapM (\ x -> frequency
        [ (1, pure [])
        , (2, (\ v -> [(x, v)]) <$> value) ]) xs
      value = do
        h  <- elements constants
        k  <- choose (0, 2)
        as <- vectorOf k (simpleExpr <$> elements (constants ++ substituted))
        return (CExpr [] [] (CSpine h as))

-- | The substitution of first-order expressions that 'substExpr' replaced:
--   it neither β-reduces nor lets the binders shadow the variables.
firstOrder :: Map String CExpr -> CExpr -> CExpr
firstOrder sub (CExpr ps ls (CSpine h as)) =
  CExpr (map substD ps) (map substD ls) $ case Map.lookup h sub of
    Just (CExpr [] _ (CSpine h' bs)) -> CSpine h' (bs ++ as')
    _                                -> CSpine h as'
  where
    as'      = map (firstOrder sub) as
    substD d = d { typ = firstOrder sub <$> typ d }

------------------------------------------------------------------------
-- * Properties
------------------------------------------------------------------------

-- | The empty substitution is the identity.
prop_substEmpty :: Expr -> Bool
prop_substEmpty (Expr e) = substExpr Map.empty e == e

-- | On first-order values, with fresh binders, 'substExpr' is the plain
--   first-order substitution.
prop_substFirstOrder :: FirstOrder -> Expr -> Bool
prop_substFirstOrder (FirstOrder sub) (Expr e) = substExpr sub e == firstOrder sub e

-- | A substituted λ is applied (one step of β-reduction), and the binders
--   shadow the substituted variables.
prop_substCases :: Bool
prop_substCases = and
  [ -- @f a [f := λ x → g x] = g a@
    substExpr (Map.fromList [("f", lam "x" (app "g" [var "x"]))]) (app "f" [var "a"])
      == app "g" [var "a"]
    -- The arguments beyond the binders are kept: @f a b [f := λ x → g x] = g a b@.
  , substExpr (Map.fromList [("f", lam "x" (app "g" [var "x"]))]) (app "f" [var "a", var "b"])
      == app "g" [var "a", var "b"]
    -- @(λ a → a) [a := b] = λ a → a@
  , substExpr (Map.fromList [("a", var "b")]) (lam "a" (var "a"))
      == lam "a" (var "a")
    -- @a c [a := f b] = f b c@
  , substExpr (Map.fromList [("a", app "f" [var "b"])]) (app "a" [var "c"])
      == app "f" [var "b", var "c"]
  ]
  where
    var       = simpleExpr
    app h as  = CExpr [] [] (CSpine h as)
    lam x b   = b { params = untyped x : params b }

------------------------------------------------------------------------
-- * All tests
------------------------------------------------------------------------

tests :: TestTree
tests = testGroup "Internal.Canonical.Types"
  [ testProperty "prop_substEmpty"      prop_substEmpty
  , testProperty "prop_substFirstOrder" prop_substFirstOrder
  , testProperty "prop_substCases"      (once prop_substCases)
  ]
