-- | Tests for "Agda.Canonical.Interval".

module Internal.Canonical.Interval ( tests ) where

import Agda.Canonical.Interval
import Agda.Canonical.Types

import Internal.Helpers

------------------------------------------------------------------------
-- * Generators
------------------------------------------------------------------------

-- | An expression of the interval over the variables @i@ and @j@.
newtype IExpr = IExpr CSpine

instance Show IExpr where
  show (IExpr sp) = show sp

instance Arbitrary IExpr where
  arbitrary = IExpr <$> sized go
    where
      go :: Int -> Gen CSpine
      go 0 = elements (map simpleSpine ["i", "j", "i0", "i1"])
      go n = frequency
        [ (1, go 0)
        , (2, op "primIMin" <$> go (n `div` 2) <*> go (n `div` 2))
        , (2, op "primIMax" <$> go (n `div` 2) <*> go (n `div` 2))
        , (1, (\ a -> CSpine "primINeg" [CExpr [] [] a]) <$> go (n - 1))
        ]
      op f a b = CSpine f [CExpr [] [] a, CExpr [] [] b]

-- | Normalises an expression of the interval.
norm :: CSpine -> CSpine
norm sp = spine (normaliseIntervals ("i0", "i1") (CExpr [] [] sp))

i, j :: CSpine
i = simpleSpine "i"
j = simpleSpine "j"

meet, join :: CSpine -> CSpine -> CSpine
meet a b = CSpine "primIMin" [CExpr [] [] a, CExpr [] [] b]
join a b = CSpine "primIMax" [CExpr [] [] a, CExpr [] [] b]

neg :: CSpine -> CSpine
neg a = CSpine "primINeg" [CExpr [] [] a]

------------------------------------------------------------------------
-- * Properties
------------------------------------------------------------------------

-- | The normal form is a normal form.
prop_idempotent :: IExpr -> Bool
prop_idempotent (IExpr e) = norm (norm e) == norm e

-- | Commutativity is taken into account.
prop_commutative :: IExpr -> IExpr -> Bool
prop_commutative (IExpr a) (IExpr b) =
  norm (meet a b) == norm (meet b a) && norm (join a b) == norm (join b a)

-- | The laws of the documentation: idempotence, absorption, De Morgan,
--   involution, and the ends of the interval.
prop_laws :: Bool
prop_laws = and
  [ norm (join i i) == i
  , norm (join i (meet i j)) == i
  , norm (neg (neg i)) == i
  , norm (neg (meet i j)) == norm (join (neg i) (neg j))
  , norm (meet i (simpleSpine "i0")) == simpleSpine "i0"
  , norm (join i (simpleSpine "i1")) == simpleSpine "i1"
    -- The interval is not a boolean algebra.
  , norm (meet i (neg i)) /= simpleSpine "i0"
  ]

------------------------------------------------------------------------
-- * All tests
------------------------------------------------------------------------

tests :: TestTree
tests = testGroup "Internal.Canonical.Interval"
  [ testProperty "prop_idempotent"  prop_idempotent
  , testProperty "prop_commutative" prop_commutative
  , testProperty "prop_laws"        (once prop_laws)
  ]
