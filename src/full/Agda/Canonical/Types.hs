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
  , ruleVars
    -- * Signatures
  , Param(..), Sig, Seen
  , GoalInfo(..), Cont(..), lookupSig
    -- * Result of @C-c C-g@
  , CanonicalResult(..), CanonicalChoices(..)
  ) where

import Control.Applicative ((<|>))
import Data.Map (Map)
import Data.Map qualified as Map

import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Common (Hiding, InteractionId, MetaId)
import Agda.Syntax.Position (Range)
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

-- | @ruleVars xs eq@ renames the variables @xs@ of a rewrite rule written by
--   hand, so that they cannot be names of the context.
--
--   Canonical takes as pattern variables of a rule the names that are not
--   in scope: a rule written with @x@ would not apply in a context that
--   has a variable @x@.  The names get a suffix @.r@, which the printing
--   removes like the one of 'Agda.Canonical.Utils.freshString'.
ruleVars :: [String] -> CEquation -> CEquation
ruleVars xs (CEquation l r b) = CEquation (sp l) (sp r) b
  where
    ren n | n `elem` xs = n ++ ".r"
          | otherwise   = n
    sp (CSpine h as)    = CSpine (ren h) (map ex as)
    ex (CExpr ps ls s)  = CExpr (map dc ps) ls (sp s)
    dc d                = d { name = ren (name d) }

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
  , giOutOfScope :: [String]
      -- ^ Context variables that the user cannot refer to, such as the
      --   implicit arguments introduced by Agda in @f = ?@.
  , giHyps    :: Map String (Bool, String)
      -- ^ Induction hypotheses added to the context (see
      --   "Agda.Canonical.Induction"), by Canonical name: the Agda call they
      --   stand for, and whether it is printed with an operator.
  , giCont    :: Maybe Cont
      -- ^ If the goal is stated through a continuation, the shape of the
      --   answer (see "Agda.Canonical.ToCanonical", goals with continuations).
  , giAliases :: Map String String
      -- ^ Names under which some symbols are in scope, e.g. @_∧_@ for
      --   @primIMin@.
  , giRefold  :: [String]
      -- ^ Variables at the end of the context refolded into the type of the
      --   goal (see 'Agda.Canonical.ToCanonical.refoldBoundary'), the first
      --   one first: the first binders of the solution stand for them.
  }

-- | The shape of an answer @λ k → k t₁ … tₙ b@ to a goal stated through a
--   continuation (see "Agda.Canonical.ToCanonical", goals with continuations),
--   whose solution is @λ Δ → b@.
data Cont = Cont
  { contOuter :: [String]
      -- ^ The binders @Δ@, declared in the context of the goal.
  , contMetas :: [MetaId]
      -- ^ The metas whose values are @t₁ … tₙ@.
  , contTyped :: Bool
      -- ^ Is @b@ preceded by its type @B@ (@S ≡ B@)?
  , contSwap  :: Int
      -- ^ The number of binders at the end of @Δ@ that come after the
      --   first binder of @b@ in the solution (see
      --   'Agda.Canonical.Cubical.commutePath').
  }

-- | Signature of a symbol; local variables shadow global symbols.
lookupSig :: GoalInfo -> String -> Maybe Sig
lookupSig gi s = Map.lookup s (giLocals gi) <|> Map.lookup s (giGlobals gi)

---------------------------------------------------------------------------
-- * Result of @C-c C-g@
---------------------------------------------------------------------------

-- | What to do with the answer of Canonical.
data CanonicalResult
  = CanonicalMessage String
      -- ^ Display a message: with @+debug@, the problem followed by the
      --   solutions; otherwise an error.
  | CanonicalGive String
      -- ^ The hole has been filled (in the type-checking state) with this
      --   expression, which remains to be written in the file.
  | CanonicalMakeCase A.QName [(A.Clause, Maybe String)]
      -- ^ Replace the clause of the hole by these clauses of the given
      --   function, produced by a case split; the right-hand side @?@ of a
      --   clause is replaced by the given text.
  | CanonicalNoResult
      -- ^ No solution was found.
  | CanonicalChoose [CanonicalResult] CanonicalChoices
      -- ^ Several solutions are accepted by Agda (with @count := n@): what
      --   each one would write ('CanonicalGive' or 'CanonicalMakeCase'),
      --   nothing being written yet, and what is needed to write the one
      --   chosen by the user (see 'Agda.Canonical.Canonical.pickCanonical').

-- | Solutions waiting for the user to choose one of them.
data CanonicalChoices = CanonicalChoices
  { ccGoal      :: InteractionId
  , ccRange     :: Range
  , ccInfo      :: GoalInfo
      -- ^ Information about the goal.
  , ccDecls     :: [CDecl]
      -- ^ The context sent to Canonical.
  , ccSelf      :: String
      -- ^ Name of the function containing the hole.
  , ccSolutions :: [(CExpr, [(MetaId, CExpr)])]
      -- ^ The solutions accepted by Agda, with the values of the metas.
  }
