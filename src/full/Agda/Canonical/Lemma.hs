-- | The lemmas of a call to Canonical: the names written in the hole, and
--   the definitions added by @+module@, @+scope@, @+file@ and
--   @(module := M)@ (see "Agda.Canonical.Options").
--
--   Like Mimer, only postulates, functions, datatypes, records and
--   primitives are added, and not the function containing the hole, nor the
--   functions mutual with it: their recursive calls are the induction
--   hypotheses (see "Agda.Canonical.Induction").

module Agda.Canonical.Lemma
  ( lemmaName
  , hintNames
  , moduleHints
  ) where

import Control.Monad (filterM, forM)
import Control.Monad.Except (catchError)
import Data.HashMap.Strict qualified as HMap
import Data.List qualified as List
import Data.List (nub)

import Agda.Canonical.Hole (holeFunction)
import Agda.Canonical.Options
import Agda.Mimer.Monad (getEverythingInScope)
import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Common
import Agda.Syntax.Concrete.Name qualified as C
import Agda.Syntax.Internal
import Agda.Syntax.Scope.Base (isNameInScopeUnqualified)
import Agda.Syntax.Scope.Monad (resolveModule)
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.MetaVars
import Agda.TypeChecking.Monad.Signature (HasConstInfo (getConstInfo))
import Agda.TypeChecking.Monad.State (getSignature)
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.List (chopWhen)

-- | The definition named by a lemma: a function, a postulate, a datatype,
--   a constructor or a projection.
lemmaName :: A.Expr -> Maybe QName
lemmaName e = case e of
  A.ScopedExpr _ e' -> lemmaName e'
  A.Def' q _        -> Just q
  A.Con c           -> Just (A.headAmbQ c)
  A.Proj _ p        -> Just (A.headAmbQ p)
  _                 -> Nothing

-- | The definitions added to the lemmas by @+module@ or @+scope@, as Mimer
--   does with @-m@ and @-u@: postulates, functions, datatypes, records and
--   primitives, of the module of the function containing the hole or in
--   scope unqualified (see 'usableHint').
hintNames :: InteractionId -> Hints -> TCM [QName]
hintNames _ NoHints = return []
hintNames ii mode = do
  mvar  <- lookupLocalMeta =<< lookupInteractionId ii
  self  <- holeFunction ii
  let scope = clScope (getMetaInfo mvar)
      wanted q = case mode of
        ModuleHints -> Just (qnameModule q) == (qnameModule <$> self)
        _           -> isNameInScopeUnqualified q scope
  filterM (usableHint self) (filter wanted (nub (getEverythingInScope mvar)))

-- | The definitions added to the lemmas by @+file@ and @(module := M)@:
--   those of the current file, and those of the modules @M@ (resolved in
--   the scope of the hole, so an alias such as @P@ of @import … as P@ is
--   accepted) and of their submodules, imported or not, in the order of
--   their declaration.  As for 'hintNames', only postulates, functions,
--   datatypes, records and primitives, and not the function containing the
--   hole.  Canonical receives their types and their clauses, as for the
--   lemmas.  An unknown module raises the usual scope error.
moduleHints :: InteractionId -> CanonicalOptions -> TCM [QName]
moduleHints ii opts
  | not (optFile opts), null (optModules opts) = return []
  | otherwise = do
      ms <- withInteractionId ii $ forM (optModules opts) $ \ m ->
              amodName <$> resolveModule (moduleQName m)
      local    <- HMap.keys . (^. sigDefinitions) <$> getSignature
      imported <- HMap.keys <$> useTC (stImports . sigDefinitions)
      self     <- holeFunction ii
      let inModules q = any (qnameModule q `isLeChildModuleOf`) ms
          names = [ q | optFile opts, q <- local ] ++ filter inModules (local ++ imported)
      filterM (usableHint self) (List.sort (nub names))
  where
    -- @A.B.C@ as a concrete qualified name.
    moduleQName m = case map C.simpleName (chopWhen (== '.') m) of
      [] -> __IMPOSSIBLE__
      xs -> foldr C.Qual (C.QName (last xs)) (init xs)

-- | Whether a definition may be added to the lemmas: a postulate, a
--   datatype, a record, a primitive, or a function other than @self@ (the
--   function containing the hole) and the functions mutual with it, and
--   other than pattern-matching λs and @with@ functions: the recursive
--   calls are the induction hypotheses.
usableHint :: Maybe QName -> QName -> TCM Bool
usableHint self q = (`catchError` \ _ -> return False) $ theDef <$> getConstInfo q <&> \case
  Axiom{}     -> True
  Datatype{}  -> True
  Record{}    -> True
  Primitive{} -> True
  Function{ funWith = NoWithFunction, funExtLam = Nothing, funMutual = m } ->
    Just q /= self && maybe True (\ s -> maybe True (s `notElem`) m) self
  _           -> False
