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
--   the ones of a projection those of the type of the projected term.  The
--   result is not a well-formed Agda term anymore, and only serves as input
--   to "Agda.Canonical.ToCanonical":
--
--   * a constructor of a datatype with parameters, applied to them, is
--     @Def c (pars ++ args)@;
--
--   * a projection or a projection-like function, applied to its
--     parameters, is @Def f (pars ++ principal : args)@.
--
--   The terms are traversed in the current context, which must be the one
--   of their free variables.  Where a type is unknown (e.g. in the body of a
--   λ whose type is not known), the term is left as it is.

module Agda.Canonical.Params
  ( restoreTerm
  , restoreEquation
  , restoreType
  , restoreTel
  , droppedParams
  ) where

import Control.Monad (foldM, guard, mzero)
import Control.Monad.Except (catchError)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Maybe (MaybeT (..))

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Context (addContext, getContextSize, typeOfBV)
import Agda.TypeChecking.Monad.MetaVars (metaType)
import Agda.TypeChecking.Monad.Signature (HasConstInfo (getConstInfo))
import Agda.TypeChecking.Reduce (reduce)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope (piApplyM)
import Agda.Utils.Impossible (__IMPOSSIBLE__)

-- | The number of parameters dropped from the applications of a projection
--   or of a projection-like function: those before its principal argument.
droppedParams :: Defn -> Int
droppedParams = \case
  Function { funProjection = Right p } | projIndex p > 0 -> projIndex p - 1
  _                                                      -> 0

---------------------------------------------------------------------------
-- * Restoration
---------------------------------------------------------------------------

-- | Restores the parameters in a type.
restoreType :: Type -> TCM Type
restoreType (El s t) = El s <$> restoreTerm Nothing t

-- | Restores the parameters in the types of a telescope.
restoreTel :: Telescope -> TCM Telescope
restoreTel EmptyTel = return EmptyTel
restoreTel (ExtendTel dom b) = do
  dom' <- traverse restoreType dom
  b'   <- case b of
    Abs x tel   -> Abs x <$> addContext (x, dom) (restoreTel tel)
    NoAbs x tel -> NoAbs x <$> restoreTel tel
  return (ExtendTel dom' b')

-- | Restores the parameters in a term, of the given type if known.
restoreTerm :: Maybe Type -> Term -> TCM Term
restoreTerm mty t = case t of
  Lam i b -> do
    mpi <- maybe (return Nothing) piView mty
    case (b, mpi) of
      (Abs x u, Just (dom, cod)) -> Lam i . Abs x <$> addContext (x, dom) (restoreTerm (Just (absBody cod)) u)
      (Abs x u, Nothing)         -> Lam i . Abs x <$> addContext (x, defaultDom __DUMMY_TYPE__) (restoreTerm Nothing u)
      (NoAbs x u, _)             -> Lam i . NoAbs x <$> restoreTerm Nothing u
  Pi a b -> do
    a' <- traverse restoreType a
    b' <- case b of
      Abs x u   -> Abs x <$> addContext (x, a) (restoreType u)
      NoAbs x u -> NoAbs x <$> restoreType u
    return (Pi a' b')
  Con c ci es -> restoreCon mty c ci es
  Var{}   -> fst <$> restoreNeutral t
  Def{}   -> fst <$> restoreNeutral t
  MetaV{} -> fst <$> restoreNeutral t
  _       -> return t

-- | Restores both sides of an equation @u = v@, at the type of the side
--   that is a neutral term (e.g. @?1 = nothing@, where @nothing@ alone does
--   not give the parameters of its type).
restoreEquation :: Term -> Term -> TCM (Term, Term)
restoreEquation u v = do
  mty <- maybe (safely Nothing (inferType v)) (return . Just) =<< safely Nothing (inferType u)
  (,) <$> restoreTerm mty u <*> restoreTerm mty v

-- | A constructor application: its parameters are those of its type.
restoreCon :: Maybe Type -> ConHead -> ConInfo -> Elims -> TCM Term
restoreCon mty c ci es = do
  def <- getConstInfo (conName c)
  let np = case theDef def of
        Constructor { conPars = n } -> n
        _                           -> __IMPOSSIBLE__
      cty = Just (defType def)
  mpars <- if np == 0 then return Nothing else maybe (return Nothing) defView mty
  case mpars of
    _ | np == 0 -> fst <$> restoreElims (Con c ci []) cty (map virtual es)
    Just (_, as) | length as >= np ->
      fst <$> restoreElims (Def (conName c) []) cty (map (Apply . defaultArg) (take np as) `prefixedTo` es)
    -- The parameters are unknown: the arguments are restored on their own.
    _ -> Con c ci <$> mapM restoreElimUntyped es
  where
    virtual e = (e, False)

-- | A neutral term, restored, and its type if known.
restoreNeutral :: Term -> TCM (Term, Maybe Type)
restoreNeutral t = case t of
  Var i es -> do
    n  <- getContextSize
    ty <- if i < n then Just <$> typeOfBV i else return Nothing
    restoreElims (Var i []) ty (map (, True) es)
  Def f es -> do
    def <- getConstInfo f
    let np  = droppedParams (theDef def)
        fty = Just (defType def)
    mpars <- case es of
      Apply r : _ | np > 0 -> safely Nothing $ maybe (return Nothing) defView =<< inferType (unArg r)
      _                    -> return Nothing
    case mpars of
      _ | np == 0 -> restoreElims (Def f []) fty (map (, True) es)
      Just (_, as) | length as >= np -> do
        (u, _) <- restoreElims (Def f []) fty (map (Apply . defaultArg) (take np as) `prefixedTo` es)
        (,) u <$> safely Nothing (inferType t)
      _ -> untyped
  MetaV m es -> do
    es' <- mapM restoreElimUntyped es
    (,) (MetaV m es') <$> safely Nothing (inferType t)
  _ -> (, Nothing) <$> restoreTerm Nothing t
  where
    untyped = case t of
      Def f es -> (, Nothing) . Def f <$> mapM restoreElimUntyped es
      _        -> __IMPOSSIBLE__

-- | Restored parameters followed by the original eliminations.  The
--   parameters are not part of the term as Agda has it ('False').
prefixedTo :: [Elim] -> Elims -> [(Elim, Bool)]
prefixedTo pars es = map (, False) pars ++ map (, True) es

-- | Restores eliminations applied to a head of the given type (if known).
--   Each elimination says whether it belongs to the term as Agda has it,
--   which is kept to compute the types.  A projection becomes an
--   application of the projection to the parameters of the record and to
--   the projected term.  Returns the restored application and its type.
restoreElims :: Term -> Maybe Type -> [(Elim, Bool)] -> TCM (Term, Maybe Type)
restoreElims h ty0 = go h h ty0
  where
    -- @raw@ is the term as Agda has it, @new@ the restored one.
    go new _ ty [] = return (new, ty)
    go new raw ty ((e, real) : rest) = case e of
      Apply a -> do
        mpi <- maybe (return Nothing) piView ty
        a'  <- restoreTerm (unDom . fst <$> mpi) (unArg a)
        let raw' = if real then raw `applyE` [e] else raw
        go (new `applyE` [Apply a { unArg = a' }]) raw' (fmap (\ (_, cod) -> absApp cod (unArg a)) mpi) rest
      Proj _ f -> do
        fdef <- getConstInfo f
        mrec <- maybe (return Nothing) defView ty
        case mrec of
          Just (_, pars) | length pars == droppedParams (theDef fdef) -> do
            let fty = defType fdef
            pars' <- restoreArgs fty pars
            ty'   <- safely Nothing (Just <$> piApplyM fty (pars ++ [raw]))
            go (Def f (map (Apply . defaultArg) (pars' ++ [new]))) (raw `applyE` [e]) ty' rest
          _ -> untypedRest
      IApply{} -> untypedRest
      where
        untypedRest = do
          es' <- mapM (restoreElimUntyped . fst) ((e, real) : rest)
          return (new `applyE` es', Nothing)

-- | Restores the arguments of a function of the given type.
restoreArgs :: Type -> [Term] -> TCM [Term]
restoreArgs _ [] = return []
restoreArgs a (u : us) = do
  mpi <- piView a
  case mpi of
    Just (dom, cod) -> do
      u'  <- restoreTerm (Just (unDom dom)) u
      us' <- restoreArgs (absApp cod u) us
      return (u' : us')
    Nothing -> mapM (restoreTerm Nothing) (u : us)

-- | Restores an elimination whose type is unknown.
restoreElimUntyped :: Elim -> TCM Elim
restoreElimUntyped = \case
  Apply a      -> Apply <$> traverse (restoreTerm Nothing) a
  IApply x y r -> IApply <$> restoreTerm Nothing x <*> restoreTerm Nothing y <*> restoreTerm Nothing r
  e            -> return e

---------------------------------------------------------------------------
-- * Types
---------------------------------------------------------------------------

-- | The type of a neutral term as Agda has it, if it can be computed.  Only
--   computed, not checked.
inferType :: Term -> TCM (Maybe Type)
inferType = runMaybeT . go
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
      IApply{} -> mzero

-- | The domain and codomain of a type, if it reduces to a Π-type.
piView :: Type -> TCM (Maybe (Dom Type, Abs Type))
piView ty = safely Nothing $ reduce (unEl ty) >>= \case
  Pi dom cod -> return (Just (dom, cod))
  _          -> return Nothing

-- | The definition and the arguments of a type that reduces to an
--   application of a definition.
defView :: Type -> TCM (Maybe (QName, [Term]))
defView ty = safely Nothing $ reduce (unEl ty) >>= \case
  Def q es | Just as <- allApplyElims es -> return (Just (q, map unArg as))
  _                                     -> return Nothing

-- | Runs a computation, returning the default value on a type error.
safely :: a -> TCM a -> TCM a
safely d m = m `catchError` \ _ -> return d
