-- | The intermediate language exchanged with Canonical.
--
--   Canonical searches for terms in a small dependent type theory, in
--   β-normal η-long form: every term is a 'CSpine' (a head symbol applied to
--   arguments) under a list of binders.  Names are plain strings, there are
--   no de Bruijn indices.
--
--   This module defines that language, the signatures used during the
--   translation from Agda ("Agda.Canonical.ToCanonical") and back
--   ("Agda.Canonical.FromCanonical"), and the result of @C-c C-g@.

module Agda.Canonical.Types
  ( -- * Canonical terms
    CDecl(..), CEquation(..), CExpr(..), CSpine(..)
  , simpleSpine, simpleExpr, typed
    -- * Signatures
  , Param(..), Sig, Seen
  , GoalInfo(..), lookupSig
    -- * Result of @C-c C-g@
  , CanonicalResult(..)
  ) where

import Control.Applicative ((<|>))
import Data.Map (Map)
import Data.Map qualified as Map

import Agda.Syntax.Common (Hiding)
import Agda.Utils.Impossible (__IMPOSSIBLE__)

---------------------------------------------------------------------------
-- * Canonical terms
---------------------------------------------------------------------------

-- | A typing judgement @name : typ@, together with equations about @name@.
--
--   In the 'params' of an expression, the equations are constraints;
--   in its 'lets', they are definitions (rewrite rules).  For instance
--
--   > not : Bool → Bool
--   > not true  = false
--   > not false = true
--
--   is represented as
--
--   > CDecl { name = "not", typ = Just (Bool → Bool)
--   >       , equations = [not true ⤇ false, not false ⤇ true] }
data CDecl = CDecl
  { name      :: String
      -- ^ Name of the symbol.
  , typ       :: Maybe CExpr
      -- ^ Type of the symbol.  If absent, Canonical does not type-check
      --   the uses of the symbol.
  , equations :: [CEquation]
      -- ^ Constraints or rewrite rules whose left-hand side is headed by the symbol.
  }

-- | An equation between two spines, e.g. @not true ⤇ false@.
data CEquation = CEquation
  { lhs     :: CSpine
      -- ^ Left-hand side; its arguments act as patterns.
  , rhs     :: CSpine
      -- ^ Right-hand side.
  , isRedex :: Bool
      -- ^ Whether the equation is used as a rewrite rule from left to right.
  }

-- | An expression, used both for types and for terms.
--
--   As a type, it reads @let lets in Π params. spine@.
--   As a term, in particular in the answers of Canonical (where 'lets' is
--   always empty), it reads @λ params. spine@.
data CExpr = CExpr
  { params :: [CDecl]
      -- ^ Binders: Π-bound for a type, λ-bound for a term.
  , lets   :: [CDecl]
      -- ^ Local definitions.  Only the goal has some: they form the
      --   context in which Canonical searches.
  , spine  :: CSpine
      -- ^ Body.
  }

-- | A head symbol applied to arguments.
data CSpine = CSpine
  { head :: String
      -- ^ Bound variable or declared symbol.
  , args :: [CExpr]
      -- ^ Arguments, all explicit.
  }

-- | A symbol without arguments.
simpleSpine :: String -> CSpine
simpleSpine s = CSpine { head = s, args = [] }

-- | A symbol without arguments nor binders.
simpleExpr :: String -> CExpr
simpleExpr s = CExpr { params = [], lets = [], spine = simpleSpine s }

-- | A declaration with a type and no equation.
typed :: String -> CExpr -> CDecl
typed n t = CDecl n (Just t) []

-- ** Printing
--
-- The output follows Canonical's own notation; it is only used to show the
-- goal sent to Canonical.  Agda syntax is produced by
-- "Agda.Canonical.FromCanonical".

instance Show CSpine where
  showsPrec p (CSpine sh sa) =
    let appPrec = 10 in
    showParen (p > appPrec && not (null sa)) $
      showString sh .
      foldr (.) id [ showChar ' ' . showsPrec (appPrec + 1) t | t <- sa ]

instance Show CEquation where
  showsPrec p CEquation{ lhs, rhs } =
    showsPrec p lhs . showString " ⤇ " . showsPrec p rhs

instance Show CExpr where
  showsPrec p CExpr{ params, spine } =
    case params of
      [] -> showsPrec p spine
      _  -> showParen (p > 0) $ showParams params . showsPrec 1 spine
    where
      showParams :: [CDecl] -> ShowS
      showParams []       = id
      showParams (d : dl) = shows d . showString " -> " . showParams dl

-- | A declaration named @Goal@ is printed as a whole problem:
--   its context, its constraints, then the goal itself.
instance Show CDecl where
  show CDecl{ name, typ, equations }
    | name /= "Goal" = "(" ++ name ++ " : " ++ maybe "_" show typ ++ ")" ++ showEqs equations
    | otherwise      = case typ of
        Nothing -> "--- Goal :\n_"
        Just e  -> showContext (lets e) ++ showConstraints equations
                   ++ "--- Goal :\n" ++ show e
    where
      showContext :: [CDecl] -> String
      showContext [] = ""
      showContext dl = "--- Context :\n" ++ showLines dl ++ "\n\n"

      showEqs :: [CEquation] -> String
      showEqs [] = ""
      showEqs l  = "{" ++ showSep l ++ "}"

      showConstraints :: [CEquation] -> String
      showConstraints [] = ""
      showConstraints el = "--- Constraints :\n" ++ concatMap ((++ "\n") . show) el ++ "\n"

      showLines :: Show a => [a] -> String
      showLines []       = __IMPOSSIBLE__
      showLines [d]      = show d
      showLines (d : dl) = show d ++ "\n" ++ showLines dl

      showSep :: Show a => [a] -> String
      showSep []       = __IMPOSSIBLE__
      showSep [d]      = show d
      showSep (d : dl) = show d ++ "; " ++ showSep dl

---------------------------------------------------------------------------
-- * Signatures
---------------------------------------------------------------------------

-- | What we need to know about a parameter of a symbol.
data Param = Param
  { pArity  :: Int
      -- ^ Number of arguments of the parameter's type (its η-long arity).
  , pHiding :: Hiding
      -- ^ Visibility of the parameter in Agda.
  }
  deriving Show

-- | The parameters of a symbol, in order.
type Sig = [Param]

-- | Symbols already declared to Canonical, with their signature.
--
--   Used to declare each symbol only once and to stop the recursion when
--   collecting definitions.
type Seen = Map String Sig

-- | What the translation back to Agda needs to know about the goal.
data GoalInfo = GoalInfo
  { giGlobals :: Map String Sig
      -- ^ Declared symbols: datatypes, constructors, functions, @Pi@, @Level@, ...
  , giLocals  :: Map String Sig
      -- ^ Variables of the context, and @Goal@.
  , giNames   :: [String]
      -- ^ Names of the context variables, the most recent first.
  }

-- | Signature of a symbol; local variables shadow global symbols.
lookupSig :: GoalInfo -> String -> Maybe Sig
lookupSig gi s = Map.lookup s (giLocals gi) <|> Map.lookup s (giGlobals gi)

---------------------------------------------------------------------------
-- * Result of @C-c C-g@
---------------------------------------------------------------------------

-- | What is displayed to the user.
data CanonicalResult
  = CanonicalExpr String
      -- ^ A message, usually the goal followed by the solutions.
  | CanonicalList [(Int, String)]
      -- ^ Numbered solutions.
  | CanonicalNoResult
      -- ^ No solution was found.
