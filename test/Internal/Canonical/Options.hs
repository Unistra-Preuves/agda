-- | Tests for "Agda.Canonical.Options".

module Internal.Canonical.Options ( tests ) where

import Data.Either (isLeft)

import Agda.Canonical.Options

import Internal.Helpers

------------------------------------------------------------------------
-- * Properties
------------------------------------------------------------------------

-- | The options as a comparable tuple.
summary :: CanonicalOptions -> (Int, Int, [String], Bool, Bool, Bool, [String])
summary o =
  ( optTimeout o, optCount o, optLemmas o, optDebug o
  , optHints o == ModuleHints, optFile o, optModules o )

-- | Parses, and summarises the result.
parsed :: String -> Either String (Int, Int, [String], Bool, Bool, Bool, [String])
parsed = fmap summary . parseCanonicalOptions

-- | An empty hole gives the default options.
prop_empty :: Bool
prop_empty = parsed "  " == Right (summary defaultCanonicalOptions)

-- | A leading number is the timeout.
prop_timeout :: NonNegative Int -> Bool
prop_timeout (NonNegative n) = (optTimeout <$> parseCanonicalOptions (show n)) == Right n

-- | All the options together, in the documented order.
prop_all :: Bool
prop_all =
  parsed "2 (count := 3) +debug +module +file (module := M.N) [+-comm, cong]"
    == Right (2, 3, ["+-comm", "cong"], True, True, True, ["M.N"])

-- | A comma inside a name with an underscore does not separate lemmas; a
--   comma followed by a space does.
prop_commas :: Bool
prop_commas =
     (optLemmas <$> parseCanonicalOptions "[_,_, a,b, c]") == Right ["_,_", "a", "b", "c"]
  && (optLemmas <$> parseCanonicalOptions "[[]]") == Right ["[]"]

-- | The unsupported flags and malformed options are rejected.
prop_errors :: Bool
prop_errors = all (isLeft . parseCanonicalOptions)
  [ "+synth", "(count := 0)", "(foo := 1)", "(count := 1", "[a] 3", "bar" ]

------------------------------------------------------------------------
-- * All tests
------------------------------------------------------------------------

tests :: TestTree
tests = testGroup "Internal.Canonical.Options"
  [ testProperty "prop_empty"   (once prop_empty)
  , testProperty "prop_timeout" prop_timeout
  , testProperty "prop_all"     (once prop_all)
  , testProperty "prop_commas"  (once prop_commas)
  , testProperty "prop_errors"  (once prop_errors)
  ]
