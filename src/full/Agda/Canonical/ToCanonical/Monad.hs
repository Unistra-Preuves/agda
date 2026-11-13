-- | The monad of the translation of a goal into a Canonical problem
--   ('TransM'), and the signatures of the symbols met ('Sym', 'Locals').
--
--   The state of the translation is the context being built and the
--   symbols already declared ('Seen'): each symbol is declared once, which
--   also stops the recursion on recursive definitions.

module Agda.Canonical.ToCanonical.Monad
  ( -- * The translation monad
    TransState(..)
  , TransM
  , pushDecls
  , pushDecl
  , currentContext
  , getSeen
  , note
  , modifySeen
  , attempt

    -- * Signatures
  , Sym(..)
  , Locals
  , localSym
  , piBinder
  , arityOf
  , termSig
  , tySig
  , constInfo
  , globalSym
  ) where

import Control.Monad (when)
import Control.Monad.State (StateT, get, gets, modify)
import Control.Monad.Trans.Maybe (MaybeT (..))
import Data.Map (Map)
import Data.Maybe (isNothing)

import Agda.Canonical.Cubical
import Agda.Canonical.Types
import Agda.Canonical.Utils
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Context (underAbstraction)
import Agda.TypeChecking.Monad.Signature (HasConstInfo (getConstInfo))
import Agda.TypeChecking.Reduce (instantiateFull)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope (telView)
import Agda.Utils.Size (size)

---------------------------------------------------------------------------
-- * The translation monad
---------------------------------------------------------------------------

-- | What the translation accumulates.
data TransState = TransState
  { tsContext :: [CDecl]
      -- ^ The context being built, the most recent declaration first (it is
      --   reversed once, when it is attached to the goal).
  , tsSeen    :: Seen
      -- ^ The symbols already declared.
  , tsNotes   :: [String]
      -- ^ What could not be translated faithfully (shown with @+debug@),
      --   the most recent first.
  }

-- | The translation.
type TransM = StateT TransState TCM

-- | Adds declarations to the context, the first one being the most recent.
pushDecls :: [CDecl] -> TransM ()
pushDecls ds = modify $ \ s -> s { tsContext = ds ++ tsContext s }

-- | Adds a declaration to the context.
pushDecl :: CDecl -> TransM ()
pushDecl d = pushDecls [d]

-- | The context built so far, in order.
currentContext :: TransM [CDecl]
currentContext = gets (reverse . tsContext)

-- | The symbols already declared.
getSeen :: TransM Seen
getSeen = gets tsSeen

-- | Records something that could not be translated faithfully.
note :: String -> TransM ()
note n = modify $ \ s -> s { tsNotes = n : tsNotes s }

-- | Records declared symbols.
modifySeen :: (Seen -> Seen) -> TransM ()
modifySeen f = modify $ \ s -> s { tsSeen = f (tsSeen s) }

-- | Runs a translation that may give up.  If it does, what it has declared
--   is forgotten.
attempt :: MaybeT TransM a -> TransM (Maybe a)
attempt m = do
  s <- get
  r <- runMaybeT m
  -- The notes are kept: they say why it gave up.
  when (isNothing r) $ modify $ \ s' -> s { tsNotes = tsNotes s' }
  return r

---------------------------------------------------------------------------
-- * Signatures
---------------------------------------------------------------------------

-- | Signatures of a symbol.
data Sym = Sym
  { symSig  :: Sig
      -- ^ Aligned with the eliminations in Agda terms: for a constructor,
      --   without the parameters of its datatype.
  , symTy   :: Maybe Type
      -- ^ Type of a definition, to compute the types of its arguments.
  , symDecl :: Sig
      -- ^ As declared to Canonical; this is the one stored in 'Seen'.
  }

-- | The local variables: their signatures, and the type of the ones bound
--   by a λ whose binder is a function as a term (see
--   'Agda.Canonical.ToCanonical.Term.toCExprAt'), with the number of
--   variables bound where this type was met.
type Locals = Map String (Sig, Maybe (Int, Type))

-- | A local variable, under @n@ bound variables: both signatures agree.
localSym :: Int -> (Sig, Maybe (Int, Type)) -> Sym
localSym n (s, mt) = Sym s ((\ (d, ty) -> raise (n - d) ty) <$> mt) s

-- | The name of a non-dependent binder: the one written by the user
--   (@(p : x ≡ y) → …@), or @a@ for an anonymous one (@A → B@).
anonName :: ArgName -> String
anonName n
  | null n || n == "_" = "a"
  | otherwise          = n

-- | A fresh name for the binder of a Π-type (see
--   'Agda.Canonical.ToCanonical.Term.underBinder').
piBinder :: Abs a -> TransM String
piBinder b = case b of
  NoAbs n _ -> freshString (anonName n)
  Abs n _   -> freshString n

-- | Number of Π-binders of a term.
arityOf :: Term -> Int
arityOf (Pi _ b) = 1 + arityOf (unEl (unAbs b))
arityOf _        = 0

-- | Syntactic signature of a type (aliases are not unfolded).
termSig :: Term -> Sig
termSig (Pi a b) = Param (arityOf (unEl (unDom a))) (getHiding a) : termSig (unEl (unAbs b))
termSig _        = []

-- | Signature of a closed type, unfolding aliases with 'telView'.
tySig :: Type -> TCM Sig
tySig t = do
  t' <- inlinePaths (unEl t)
  TelV tel _ <- telView (El (getSort t) t')
  go tel
  where
    go :: Telescope -> TCM Sig
    go EmptyTel = return []
    go (ExtendTel dom b) = do
      TelV d _ <- telView (unDom dom)
      rest <- underAbstraction dom b go
      return (Param (size d) (getHiding dom) : rest)

-- | A definition, with the metas solved since it was checked instantiated
--   (e.g. the implicit arguments in the type of a postulate of the file).
constInfo :: QName -> TCM Definition
constInfo q = instantiateFull =<< getConstInfo q

-- | Signatures of a definition or a constructor.
globalSym :: QName -> TCM Sym
globalSym q = do
  def <- constInfo q
  sg  <- tySig (defType def)
  case theDef def of
    ConstructorDefn cd -> return (Sym (drop (_conPars cd) sg) Nothing sg)
    _                  -> return (Sym sg (Just (defType def)) sg)
