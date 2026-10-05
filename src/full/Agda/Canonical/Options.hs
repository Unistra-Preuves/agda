-- | Options of the @C-c C-g@ command.
--
--   They are written inside the hole, in the format of the Lean
--   @canonical@ tactic:
--
--   > {! [timeout] [(count := n)] [+debug] [[lem₁, lem₂, …]] !}
--
--   For instance @{! 10 (count := 3) [+-comm, cong] !}@.
--   By default the solution is written in the file; with @+debug@, the
--   problem sent to Canonical and its solutions are only displayed.

module Agda.Canonical.Options
  ( CanonicalOptions(..)
  , defaultCanonicalOptions
  , canonicalUsage
  , parseCanonicalOptions
  ) where

import Data.Char (isDigit, isSpace)
import Data.List (dropWhileEnd, stripPrefix)
import Text.Read (readMaybe)

-- | Options of a call to Canonical.
data CanonicalOptions = CanonicalOptions
  { optTimeout :: Int
      -- ^ Search time limit, in seconds.
  , optCount   :: Int
      -- ^ Number of solutions to search for.
  , optLemmas  :: [String]
      -- ^ Names to add to the context of Canonical, as written by the user.
  , optDebug   :: Bool
      -- ^ Display the problem and the solutions instead of writing a solution.
  }

-- | Five seconds, one solution, no lemma, no debug.
defaultCanonicalOptions :: CanonicalOptions
defaultCanonicalOptions = CanonicalOptions
  { optTimeout = 5
  , optCount   = 1
  , optLemmas  = []
  , optDebug   = False
  }

-- | Reminder of the syntax, shown with parse errors.
canonicalUsage :: String
canonicalUsage = "Usage: {! [timeout] [(count := n)] [+debug] [[lem₁, lem₂, …]] !}"

-- | Parses the content of the hole.
--
--   The list of lemmas must come last, since a name like @[]@ may occur in it.
--   The only flag is @+debug@ (or @-debug@); the other Lean flags, such as
--   @+synth@, are rejected: the Agda interface of Canonical only takes a
--   timeout and a number of solutions.
parseCanonicalOptions :: String -> Either String CanonicalOptions
parseCanonicalOptions = go defaultCanonicalOptions . trim
  where
    go o "" = Right o
    go o s@(c : _) | isDigit c =
      let (n, r) = span isDigit s in go o { optTimeout = read n } (trim r)
    go o ('(' : r) = case break (== ')') r of
      (inside, ')' : r') -> config o inside >>= \ o' -> go o' (trim r')
      _                  -> Left "missing closing parenthesis"
    go o ('[' : r) = case break (== ']') (reverse r) of
      (after, ']' : inside) | all isSpace after ->
        Right o { optLemmas = optLemmas o ++ lemmaNames (reverse inside) }
      _ -> Left "the list of lemmas must be closed by ] and come last"
    go o (c : r) | c `elem` ("+-" :: String) =
      let (flag, r') = break isSpace r in
      if flag == "debug" then go o { optDebug = c == '+' } (trim r')
      else Left ("option " ++ c : flag ++ " is not supported in Agda")
    go _ s = Left ("invalid option: " ++ takeWhile (not . isSpace) s)

    -- @(key := value)@
    config o inside = case break (== ':') inside of
      (k, ':' : '=' : v) -> case (trim k, readMaybe (trim v)) of
        ("count",   Just n) | n > 0  -> Right o { optCount = n }
        ("timeout", Just n) | n >= 0 -> Right o { optTimeout = n }
        (key, _)
          | key `elem` ["count", "timeout"] -> Left ("invalid value for option " ++ key)
          | otherwise                       -> Left ("unknown option: " ++ key)
      _ -> Left ("invalid option: (" ++ inside ++ ")")

    -- Lemmas are separated by commas.  Since an Agda name may contain a
    -- comma (@_,_@), a comma inside a word only separates names when the
    -- word contains no underscore.
    lemmaNames = concatMap splitWord . words
    splitWord w = case stripTrailingComma w of
      ""                                   -> []
      w' | ',' `elem` w', '_' `notElem` w' -> filter (not . null) (splitOn ',' w')
         | otherwise                       -> [w']
    stripTrailingComma w
      | w == ","                                = ""
      | Just w' <- stripSuffix "," w, w' /= "_" = w'
      | otherwise                               = w
    stripSuffix suf w = reverse <$> stripPrefix (reverse suf) (reverse w)
    splitOn c s = case break (== c) s of
      (a, _ : r) -> a : splitOn c r
      (a, [])    -> [a]
    trim = dropWhileEnd isSpace . dropWhile isSpace
