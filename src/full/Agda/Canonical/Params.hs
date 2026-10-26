-- | Restoration of the parameters that Agda leaves out of its internal syntax.
--
--   Agda does not store, in its terms:
--
--   * the parameters of a constructor: @x ∷ xs@ is @Con _∷_ [x, xs]@, without
--     the type @A@ of the elements;
--
--   * the parameters of a record projection: @r .fst@ is @r@ eliminated by
--     @Proj fst@, without the parameters @A B@ of @A × B@;
--
--   * the parameters of a projection-like function (a function whose first
--     arguments are the parameters of the datatype of a later argument, see
--     "Agda.TypeChecking.ProjectionLike"), dropped from its applications
--     and from the patterns of its clauses.
--
--   Canonical has no such implicit parameters: every symbol is applied to
--   all its arguments.  This module puts them back, computing them from the
--   types: the parameters of a constructor are those of its expected type,
--   the ones of a projection those of the type of the projected term.
--
--   Only the application at the root of a term is restored ('restoreRoot'):
--   "Agda.Canonical.ToCanonical" restores each subterm when it translates it,
--   in its context.  The terms it works on thus stay as Agda has them, and
--   can be reduced (to unfold a path type, a Π-type…) without bringing back
--   unrestored subterms, or reducing a term that is not one of Agda.  The
--   restored root is not a well-formed Agda term anymore:
--
--   * a constructor of a datatype with parameters, applied to them, is
--     @Def c (pars ++ args)@;
--
--   * a projection or a projection-like function, applied to its
--     parameters, is @Def f (pars ++ principal : args)@.
--
--   The parameters and the arguments are terms as Agda has them.  The
--   current context must be the one of the free variables of the term.

module Agda.Canonical.Params
  ( restoreRoot
  , inferType
  , droppedParams
  ) where

import Control.Monad (foldM, guard, mzero)
import Control.Monad.Except (catchError)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Maybe (MaybeT (..))

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Builtin (pathView)
import Agda.TypeChecking.Monad.Context (getContextSize, typeOfBV)
import Agda.TypeChecking.Monad.MetaVars (metaType)
import Agda.TypeChecking.Monad.Signature (HasConstInfo (getConstInfo))
import Agda.TypeChecking.Reduce (instantiateFull, reduce)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope (piApplyM)

-- | The number of parameters dropped from the applications of a projection
--   or of a projection-like function: those before its principal argument.
droppedParams :: Defn -> Int
droppedParams = \case
  Function { funProjection = Right p } | projIndex p > 0 -> projIndex p - 1
  _                                                      -> 0

---------------------------------------------------------------------------
-- * Restoration
---------------------------------------------------------------------------

-- | Restores the parameters of the application at the root of a term, of
--   the given type if known (which a constructor needs).  The term is left
--   as it is where the parameters are unknown.
--
--   With several projections (@r .f .g@), the last one is the root: its
--   principal argument @r .f@ is restored in turn when it is translated.
restoreRoot :: Maybe Type -> Term -> TCM Term
restoreRoot mty t = case t of
  Con c _ es -> do
    def <- getConstInfo (conName c)
    let np = case theDef def of
          Constructor { conPars = n } -> n
          _                           -> 0
    if np == 0 then return t else do
      mpars <- maybe (return Nothing) defView mty
      return $ case mpars of
        Just (_, as) | length as >= np -> Def (conName c) (map (Apply . defaultArg) (take np as) ++ es)
        _                              -> t
  Var i es   -> neutral (Var i) es
  Def f es   -> neutral (Def f) es
  MetaV m es -> neutral (MetaV m) es
  _          -> return t
  where
    neutral h es = case lastProj es of
      -- @r .f es'@ is @f pars r es'@.
      Just (pre, f, post) -> do
        let r = h pre
        mpars <- principalParams f r
        return $ case mpars of
          Just pars -> Def f (map (Apply . defaultArg) (pars ++ [r]) ++ post)
          Nothing   -> t
      Nothing -> case (h [], es) of
        -- A projection-like function, applied to its principal argument.
        (Def f [], Apply r : _) -> do
          mpars <- principalParams f (unArg r)
          return $ case mpars of
            Just pars -> Def f (map (Apply . defaultArg) pars ++ es)
            Nothing   -> t
        _ -> return t

-- | The eliminations before the last projection, the projection and the
--   ones after it.
lastProj :: Elims -> Maybe (Elims, QName, Elims)
lastProj es = case break isProj (reverse es) of
  (post, Proj _ f : pre) -> Just (reverse pre, f, reverse post)
  _                      -> Nothing
  where
    isProj Proj{} = True
    isProj _      = False

-- | The parameters dropped from an application of a projection or of a
--   projection-like function @f@ to the principal argument @r@: those of the
--   type of @r@.  @Just []@ if @f@ has none.
principalParams :: QName -> Term -> TCM (Maybe [Term])
principalParams f r = do
  np <- droppedParams . theDef <$> getConstInfo f
  if np == 0 then return (Just []) else do
    mrec <- maybe (return Nothing) defView =<< inferType r
    return $ case mrec of
      Just (_, pars) | length pars >= np -> Just (take np pars)
      _                                  -> Nothing

---------------------------------------------------------------------------
-- * Types
---------------------------------------------------------------------------

-- | The type of a neutral term as Agda has it, if it can be computed.  Only
--   computed, not checked.
inferType :: Term -> TCM (Maybe Type)
inferType = safely Nothing . runMaybeT . go
  where
    go :: Term -> MaybeT TCM Type
    go t = case t of
      Var i es -> do
        n <- lift getContextSize
        guard (i < n)
        a <- lift (typeOfBV i)
        elimsType (Var i []) a es
      Def f es -> do
        def <- lift (getConstInfo f)
        let np = droppedParams (theDef def)
        pars <- if np == 0 then return [] else case es of
          Apply r : _ -> do
            (_, as) <- MaybeT . defView =<< go (unArg r)
            guard (length as >= np)
            return (take np as)
          _ -> mzero
        a <- foldM (\ b u -> lift (piApplyM b u)) (defType def) pars
        elimsType (Def f []) a es
      MetaV m es -> do
        a <- lift (metaType m)
        elimsType (MetaV m []) a es
      _ -> mzero

    elimsType _ a [] = return a
    elimsType h a (e : es) = case e of
      Apply u -> do
        a' <- lift (piApplyM a (unArg u))
        elimsType (h `applyE` [e]) a' es
      Proj _ f -> do
        (_, pars) <- MaybeT (defView a)
        fdef <- lift (getConstInfo f)
        a' <- lift (piApplyM (defType fdef) (pars ++ [h]))
        elimsType (h `applyE` [e]) a' es
      -- A path applied to the interval: @A r@ for @PathP A x y@.
      IApply _ _ r -> do
        PathType { pathSort = s, pathType = fam } <- lift . pathView . El (getSort a) =<< lift (reduce (unEl a))
        elimsType (h `applyE` [e]) (El s (unArg fam `apply` [defaultArg r])) es

-- | The definition and the arguments of a type that reduces to an
--   application of a definition.  The metas solved since the type was
--   built are instantiated in the arguments: a parameter must not be a
--   solved meta (the level @_42@ of @Maybe _42 Bool@, already @lzero@),
--   which Canonical could not match with its value.
defView :: Type -> TCM (Maybe (QName, [Term]))
defView ty = safely Nothing $ reduce (unEl ty) >>= \case
  Def q es | Just as <- allApplyElims es -> Just . (q,) <$> instantiateFull (map unArg as)
  _                                     -> return Nothing

-- | Runs a computation, returning the default value on a type error.
safely :: a -> TCM a -> TCM a
safely d m = m `catchError` \ _ -> return d
