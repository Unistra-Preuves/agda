-- | The translation of terms, types and definitions (see
--   "Agda.Canonical.ToCanonical" for the conventions).
--
--   The translation of a term declares the definitions it meets
--   ('declareDef'), with their clauses as rewrite rules: the functions of
--   this module are mutually recursive.

module Agda.Canonical.ToCanonical.Term
  ( -- * Declarations
    DeclKind(..)
  , declare
  , declareDef
  , declaredName
  , unfoldPis

    -- * Terms
  , toCType
  , toCExpr
  , toCExprAt
  , inferHere
  , underBinder
  , sortLevel
  , isPi

    -- * Metas
  , closedMetaType

    -- * Cubical Agda
  , isCubicalOp
  , mentionsEmptyFace
  ) where

import Control.Monad (foldM, forM, guard, replicateM, unless, when, zipWithM)
import Control.Monad.Except (catchError)
import Control.Monad.State (gets, lift, modify)
import Control.Monad.Trans.Maybe (MaybeT (..))
import Data.List (isSuffixOf, mapAccumL)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (catMaybes, listToMaybe)

import Agda.Canonical.Builtin
import Agda.Canonical.Cubical
import Agda.Canonical.Params (droppedParams, inferType, restoreRoot)
import Agda.Canonical.Recursor (mkRecursor)
import Agda.Canonical.ToCanonical.Monad
import Agda.Canonical.ToCanonical.Pattern
import Agda.Canonical.Types
import Agda.Canonical.Utils
import Agda.Syntax.Builtin
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty qualified as P
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Generic (foldTerm)
import Agda.Syntax.Internal.MetaVars (noMetas)
import Agda.Syntax.Internal.Names (namesIn)
import Agda.Syntax.Literal (Literal (..))
import Agda.TypeChecking.Free (freeIn)
import Agda.TypeChecking.Level (reallyUnLevelView)
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Context (addContext, getContextSize, inTopContext, typeOfBV)
import Agda.TypeChecking.Monad.MetaVars (lookupLocalMeta')
import Agda.TypeChecking.Monad.Signature (HasConstInfo (getConstInfo))
import Agda.TypeChecking.Reduce (instantiateFull, reduce)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope (teleNames, telView, telViewUpTo)
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Maybe (fromMaybe, whenJust)
import Agda.Utils.Monad (anyM, unlessM)

---------------------------------------------------------------------------
-- * Π-types as terms
---------------------------------------------------------------------------

-- | Declares @Pi@, and @Level@ and @_⊔_@ on which it depends, if not done yet.
declarePi :: TransM ()
declarePi = do
  unlessM (seenMember "Pi" <$> getSeen) $ do
    lq <- fromMaybe __IMPOSSIBLE__ <$> getName' BuiltinLevel
    mq <- fromMaybe __IMPOSSIBLE__ <$> getName' PrimLevelMax
    modifySeen $ \ s -> foldr (uncurry seenInsert) s piSigs
    mapM_ declareDef [lq, mq]
    pushDecls piDecls

-- | The common arguments of @Pi@, @Pi.mk@ and @Pi.f@.
data PiP = PiP
  { ppLu :: CExpr  -- ^ Level of the domain.
  , ppLv :: CExpr  -- ^ Level of the codomain.
  , ppA  :: CExpr  -- ^ Domain.
  , ppB  :: CExpr  -- ^ Codomain, as a family @λ x. B@.
  }

-- | The arguments of a 'PiP', in order.
piArgs :: PiP -> [CExpr]
piArgs p = [ppLu p, ppLv p, ppA p, ppB p]

-- | Level of a sort; @lzero@ for the sorts Canonical does not know.
sortLevel :: HasBuiltins m => Sort -> m Term
sortLevel (Type l) = reallyUnLevelView l
sortLevel (SSet l) = reallyUnLevelView l
sortLevel (Prop l) = reallyUnLevelView l
sortLevel _        = return (Level (Max 0 []))

-- | Translates the components of a Π-type @(x : A) → B@.
piParts :: Dom Type -> Abs Type -> [String] -> Locals -> TransM PiP
piParts a b names locals = do
  x <- freshString $ case b of
    NoAbs _ _ -> "a"
    Abs n _   -> n
  lu <- sortLevel (getSort (unDom a))
  eu <- toCExpr lu names  locals
  ea <- toCExpr (unEl $ unDom a) names locals
  let locals' = Map.insert x (termSig (unEl $ unDom a), Nothing) locals
  (ev, eb) <- underBinder x a b names $ \ names' -> do
    lv <- sortLevel (getSort (unAbs b))
    (,) <$> toCExpr lv names' locals
        <*> toCExprAt Nothing (unEl $ unAbs b) names' [untyped x] locals'
  declarePi
  return (PiP eu ev ea eb)

-- | Translates under the binder of an abstraction, named @x@: if it binds a
--   variable, it is added to the bound names, and to the context of Agda
--   with the type @a@ (see 'restoreRoot').
underBinder :: String -> Dom Type -> Abs b -> [String] -> ([String] -> TransM c) -> TransM c
underBinder x a b names k = case b of
  Abs{}   -> addContext (x, a) (k (x : names))
  NoAbs{} -> k names

---------------------------------------------------------------------------
-- * Applications
---------------------------------------------------------------------------

-- | The terms of the applications in a list of eliminations.
appliedTerms :: [Elim' Term] -> [Term]
appliedTerms es = concatMap arg es
  where
    arg (Apply t)      = [unArg t]
    arg (IApply _ _ r) = [r]   -- a path is a function of the interval
    arg _              = []

-- | The successive types before each argument, instantiated: a Π-type, or
--   a path type for an argument of the interval (the path is applied to
--   it).  A type that is neither is reduced.
fnTypes :: Type -> [Term] -> TCM [Type]
fnTypes _ [] = return []
fnTypes t (a : as) = case unEl t of
  Pi _ b -> (t :) <$> fnTypes (absApp b a) as
  _ -> do
    t' <- reduce (unEl t)
    pv <- pathView (El (getSort t) t')
    case (t', pv) of
      (Pi{}, _) -> fnTypes (El (getSort t) t') (a : as)
      (_, PathType { pathSort = s, pathType = fam }) ->
        (El s t' :) <$> fnTypes (El s (unArg fam `apply` [defaultArg a])) as
      _ -> return []
  `catchError` \ _ -> return []

-- | @stripPi ps t@ removes @length ps@ Π-binders from @t@, binding their
--   variables to the names @ps@.  Returns the binders that bind a variable,
--   the first one first (see 'underBinders').
stripPi :: [String] -> Term -> Maybe ([(String, Dom Type)], Term)
stripPi [] t = Just ([], t)
stripPi (p : ps) (Pi a b) = do
  (bs, t) <- stripPi ps (unEl (unAbs b))
  return $ case b of
    Abs{}   -> ((p, a) : bs, t)
    NoAbs{} -> (bs, t)
stripPi _ _ = Nothing

-- | 'stripPi', reducing the type until it shows its Π-binders (e.g. a
--   definition that unfolds into a Π-type), and the type after them.
stripPiR :: [String] -> Term -> TCM (Maybe ([(String, Dom Type)], Term))
stripPiR ps t = reduce t >>= \ t' -> case (ps, t') of
  ([], _) -> return (Just ([], t'))
  (p : ps', Pi a b) -> do
    r <- addContext (p, a) (stripPiR ps' (unEl (unAbs b)))
    return $ r <&> \ (bs, u) -> case b of
      Abs{}   -> ((p, a) : bs, u)
      NoAbs{} -> (bs, u)
  _ -> return Nothing
  `catchError` \ _ -> return Nothing

-- | 'underBinder' for several binders, the first one first.
underBinders :: [(String, Dom Type)] -> [String] -> ([String] -> TransM c) -> TransM c
underBinders [] names k = k names
underBinders ((x, a) : bs) names k = addContext (x, a) (underBinders bs (x : names) k)

-- | Adapts an argument to the expected arity @k@.
--
--   With fewer binders, the argument is a Π-type as a term (@Pi u v A B@):
--   it is η-expanded through @Pi.f@, e.g. @λ z → Pi.f u v A B x z@ for a
--   variable @x@ bound by a λ whose binder is a function as a term, or for
--   @fst e@ with @e : Σ (A → B) P@.  (The arguments are translated in
--   η-long form for their own heads, so that a missing binder is one of
--   such a Π-type.)  It is η-expanded plainly when the expected type is not
--   known.  With more binders, the extra ones are wrapped in @Pi.mk@: the
--   parameter has a Π-type as a term.
fixArg :: [String] -> Int -> Maybe Term -> CExpr -> Locals -> TransM CExpr
fixArg names k mty ce@(CExpr ps ls sp) locals
  | m == k = return ce
  | m < k  = do
      -- The binder of the expected type after the @m@ ones of the argument.
      next <- case mty of
        Nothing -> return Nothing
        Just ty -> lift (stripPiR (map name ps) ty)
      case next of
        Just (bs, Pi dom b) -> do
          z  <- freshString (case b of { Abs y _ -> y; NoAbs{} -> "z" })
          sp' <- underBinders bs names $ \ names' -> do
            pp <- piParts dom b names' locals
            ez <- etaVar z (arityOf (unEl (unDom dom)))
            return $ CSpine "Pi.f" (piArgs pp ++ [CExpr [] [] sp, ez])
          fixArg names k mty (CExpr (ps ++ [untyped z]) ls sp') locals
        _ -> etaExtend (k - m) ce
  | otherwise =
      case mty >>= stripPi (map name outer) of
        Just (bs, Pi dom b) -> underBinders bs names $ \ names' -> do
          pp     <- piParts dom b names' locals
          inner' <- fixArg names' 1 (Just (Pi dom b)) (CExpr inner [] sp) locals
          return $ CExpr outer ls (CSpine "Pi.mk" (piArgs pp ++ [inner']))
        _ -> return ce
  where
    m = length ps
    (outer, inner) = splitAt k ps

-- | Applies a head symbol to its translated arguments, in η-long form.
--
--   Each argument is adapted to the arity expected by the signature
--   ('fixArg').  Missing arguments become fresh binders, returned so that
--   the caller adds them to the enclosing λ.  Arguments beyond the
--   signature (the head returns a Π-type as a term) are applied with @Pi.f@,
--   and the interval arguments of a path type as a term with @Path.f@.
applyHead
  :: String          -- ^ Head symbol.
  -> Maybe Sym       -- ^ Its signatures, if known.
  -> [Term]          -- ^ The Agda arguments.
  -> [CExpr]         -- ^ The same arguments, translated.
  -> [String]        -- ^ Bound names.
  -> Locals
  -> TransM (CSpine, [CDecl])
       -- ^ The spine, and the binders added by η-expansion.
applyHead hd Nothing _ cargs _ _ = return (CSpine hd cargs, [])
applyHead hd (Just Sym { symSig = sg, symTy = mty }) terms cargs names locals = do
  ftys <- lift $ maybe (return []) (`fnTypes` terms) mty
  let ar   = length sg
      n    = length cargs
      expected i = case drop i ftys of
        (t : _) | Pi dom _ <- unEl t -> Just (unEl (unDom dom))
        _                            -> Nothing
      -- An argument beyond the signature, applied with @Pi.f@, or with
      -- @Path.f@ (to @ℓ A x y@, the arguments of @PathP@).
      extraArg g (i, ce) = case drop i ftys of
        (t : _) | Pi dom b <- unEl t -> do
          let dty = unEl (unDom dom)
          pp  <- piParts dom b names locals
          ce' <- fixArg names (arityOf dty) (Just dty) ce locals
          return $ CSpine "Pi.f" (piArgs pp ++ [CExpr [] [] g, ce'])
        (t : _) -> pathView t >>= \case
          PathType { pathName = q, pathLevel = l, pathType = a, pathLhs = x, pathRhs = y } -> do
            (CSpine _ pas, _) <- toCSpine Nothing (Def q (map Apply [l, a, x, y])) names locals
            return $ CSpine "Path.f" (pas ++ [CExpr [] [] g, ce])
          OType{} -> return $ appendArg g ce
        _ -> return $ appendArg g ce
  fixed <- sequence [ fixArg names k (expected i) ce locals
                    | (i, k, ce) <- zip3 [0 ..] (map pArity sg) cargs ]
  xs    <- replicateM (max 0 (ar - n)) (freshString "x")
  etas  <- zipWithM etaVar xs (map pArity (drop n sg))
  sp    <- foldM extraArg (CSpine hd (fixed ++ etas)) (zip [ar ..] (drop ar cargs))
  return (sp, map untyped xs)
  where
    appendArg (CSpine h as) ce = CSpine h (as ++ [ce])

---------------------------------------------------------------------------
-- * Terms
---------------------------------------------------------------------------

-- | The role of a declaration, which decides what the equations of its
--   path boundary are.
data DeclKind
  = Parameter
      -- ^ A parameter: its equations are constraints on its instances.
  | Definition
      -- ^ A declaration of the context: its equations are rewrite rules.
  deriving Eq

-- | Translates a type into a declaration, and records its signature.
--
--   In Cubical Agda, the path types in type positions become functions of
--   the interval; if the type is a path type @PathP A x y@, its boundary
--   @n i0 ≡ x@, @n i1 ≡ y@ is added to the equations (see 'pathEquations').
declare
  :: DeclKind
  -> Term            -- ^ The type of the declaration.
  -> String          -- ^ Its name.
  -> [CEquation]     -- ^ Its equations.
  -> [String]        -- ^ Bound names.
  -> Locals
  -> TransM (CDecl, Locals)
declare kind t0 n eqs names locals = do
  t    <- lift $ unfoldPis =<< inlinePaths t0
  ty   <- toCType t names locals
  peqs <- pathEquations kind n ty t0 names locals
  return (CDecl n (Just ty) (eqs ++ peqs), Map.insert n (termSig t, Nothing) locals)

-- | Unfolds the definitions that stand for Π-types (@X = (P : Set₁) → (A → P) → P@)
--   in the type of a declaration, so that its binders are parameters.  The
--   other definitions are not unfolded.
unfoldPis :: Term -> TCM Term
unfoldPis t = do
  t' <- reduce t `catchError` \ _ -> return t
  case t' of
    Pi a b -> do
      b' <- traverse (\ (El s u) -> El s <$> unfoldPis u) b
      return (Pi a b')
    _ -> return t

-- | The boundary of a declaration @n : Δ → PathP A x y@, translated as
--   @n : Δ → (i : I) → A i@ with the type @ty@:
--
--   > n δ i0 ⤇ x        n δ i1 ⤇ y
--
--   η-expanded if @A@ is a function type.  As constraints (for a
--   'Parameter'), these equations cannot bind variables: they are only
--   given when @Δ@ and the arguments of @A@ are empty.
pathEquations :: DeclKind -> String -> CExpr -> Term -> [String] -> Locals -> TransM [CEquation]
pathEquations kind n ty t0 names locals = pathEnds t0 >>= \case
  Just (k, x, y)
    | length (params ty) > k
    , let outer = map name (take k (params ty))
    , Just (bs, pt) <- stripPi outer t0 -> do
    (i0, i1) <- intervalEnds
    zero <- primIZero
    one  <- primIOne
    let extra = length (params ty) - k - 1
        -- @x : A i0@ and @y : A i1@, in the context of @Δ@.
        end i r u = underBinders bs names $ \ names' -> do
          pv <- pathView . El anySort =<< reduce pt
          let ex = case pv of
                PathType { pathSort = s, pathType = a } ->
                  let at = El s (unArg a `apply` [defaultArg r]) in Just (at, at)
                OType{} -> Nothing
          eu <- etaTo extra =<< toCExprAt ex u names' [] locals
          let xs  = map name (params eu)
              lhs = CSpine n (map simpleExpr (outer ++ [i] ++ xs))
              ok  = length xs == extra && (kind == Definition || (k == 0 && extra == 0))
          return [ CEquation lhs (spine eu) True | ok ]
    concat <$> sequence [end i0 zero x, end i1 one y]
  _ -> return []

-- | Translates a type: its Π-binders become parameters.
toCType :: Term -> [String] -> Locals -> TransM CExpr
toCType = go []
  where
    go ps (Pi a b) names locals = do
      x <- piBinder b
      (d, locals') <- declare Parameter (unEl $ unDom a) x [] names locals
      underBinder x a b names $ \ names' -> go (d : ps) (unEl $ unAbs b) names' locals'
    go ps t names locals = toCExprAt Nothing t names ps locals

-- | Translates a term.  A Π-type is encoded with @Pi@; λ-binders become
--   parameters.
toCExpr :: Term -> [String] -> Locals -> TransM CExpr
toCExpr t names = toCExprAt Nothing t names []

-- | 'toCExpr' under the given parameters (the most recent first), given the
--   type expected for the term if known, both as declared and as
--   instantiated (e.g. @(a : X) → Set@ and @(a : X → X) → Set@ for the
--   second argument of @Σ-i@ at @X := X → X@).  A λ-binder whose declared
--   type is not a Π-type but whose instantiated type is one is a function
--   as a term (@Pi u v A B@): its applications go through @Pi.f@, and its
--   type is recorded for that.
toCExprAt :: Maybe (Type, Type) -> Term -> [String] -> [CDecl] -> Locals -> TransM CExpr
toCExprAt ex t names ps locals = case t of
  Pi a b -> do
    pp <- piParts a b names locals
    return $ CExpr (reverse ps) [] (CSpine "Pi" (piArgs pp))
  Lam _ b -> do
    -- A fresh name, which cannot capture a variable of the context (the
    -- binder @p@ of a constraint would capture the path @p@).
    x <- case b of
      NoAbs _ _ -> return "_"
      Abs y _   -> freshString y
    (ex', dom, bty, locals') <- lamBinder ex x b names locals
    underBinder x dom b names $ \ names' ->
      toCExprAt ex' (unAbs b) names' (CDecl x bty [] : ps) locals'
  _ -> termBinder ex >>= \case
    -- A function whose first binder is a function as a term (the family
    -- @P@ of @Σ (A → B) P@) is η-expanded first, so that this binder is
    -- one (see 'lamBinder'): @λ x → P (λ z → Pi.f … x z)@.
    Just dom -> toCExprAt ex (Lam (domInfo dom) (Abs "x" (raise 1 t `apply` [Arg (domInfo dom) (var 0)])))
                          names ps locals
    Nothing -> do
      (sp, extra) <- toCSpine (snd <$> ex) t names locals
      return $ CExpr (reverse ps ++ extra) [] sp

-- | The first binder of the expected type @ex@ (see 'toCExprAt'), if it is
--   a function as a term: its declared type is not a Π-type (nor @Partial@),
--   and its instantiated type reduces to one.
termBinder :: Maybe (Type, Type) -> TransM (Maybe (Dom Type))
termBinder Nothing = return Nothing
termBinder (Just (raw, inst)) = do
  r <- reduce (unEl raw)
  i <- reduce (unEl inst)
  case (r, i) of
    (Pi rd _, Pi idom _) -> do
      bt      <- reduce (unEl (unDom idom))
      partial <- isPartial (unEl (unDom rd))
      return $ if not (isPi (unEl (unDom rd)) || partial) && isPi bt then Just idom else Nothing
    _ -> return Nothing

-- | The binder of a λ whose type is expected to be @ex@ (see 'toCExprAt'):
--   the type expected for its body, the type of the binder in Agda (a dummy
--   one if unknown), its type if it is a function as a term, and the local
--   variables under it.  @x@ is the name given to the binder.
lamBinder :: Maybe (Type, Type) -> String -> Abs Term -> [String] -> Locals
          -> TransM (Maybe (Type, Type), Dom Type, Maybe CExpr, Locals)
lamBinder Nothing _ _ _ locals = return (Nothing, defaultDom __DUMMY_TYPE__, Nothing, locals)
lamBinder (Just (raw, inst)) x b names locals = do
  r <- reduce (unEl raw)
  i <- reduce (unEl inst)
  case (r, i) of
    (Pi rd rb, Pi idom ib) -> do
      bt <- reduce (unEl (unDom idom))
      let next = case b of
            Abs{}   -> Just (absBody rb, absBody ib)
            NoAbs{} -> (,) <$> noAbsBody rb <*> noAbsBody ib
      -- @Partial φ A@ is a function type, as in the context.
      partial <- isPartial (unEl (unDom rd))
      if isPi (unEl (unDom rd)) || partial || not (isPi bt) then return (next, idom, Nothing, locals) else do
        -- The type of a function as a term is given to the binder.
        e <- toCExpr bt names locals
        let locals' = case b of
              Abs{}   -> Map.insert x ([], Just (length names, El (getSort (unDom idom)) bt)) locals
              NoAbs{} -> locals
        return (next, idom, Just e, locals')
    _ -> return (Nothing, defaultDom __DUMMY_TYPE__, Nothing, locals)

-- | Translates a neutral term or a sort, of the given type if known.
--
--   The parameters left out by Agda are first put back at its root (see
--   'restoreRoot').  Returns the binders added by η-expansion (see
--   'applyHead').  Unsupported terms are opaque constants, named by their
--   printed form.
toCSpine :: Maybe Type -> Term -> [String] -> Locals -> TransM (CSpine, [CDecl])
toCSpine _ (Def q es) names locals | Just h <- auxName q = auxSpine h es names locals
toCSpine mty t0 names locals = restored mty t0 names >>= \ t -> case t of
  Var i es -> do
    -- The arguments are expected at the types given by the one of the
    -- variable.
    mvt  <- boundType i names
    exps <- lift $ maybe (return []) (\ a -> argTypes a a (appliedTerms es)) mvt
    as   <- elimsToCExprAt exps es names locals
    let h = names !! i
    applyHead h (localSym (length names) <$> Map.lookup h locals) (appliedTerms es) as names locals
  MetaV m es
    -- A meta of the goal (see "Goals with metas"), applied to its context.
    | Map.member (metaVarName m) locals -> localApp m es
    | otherwise -> foreignMeta m es
  Sort (MetaS m es) -> foreignMeta m es
  Sort (Type l) -> universe "Type" l
  Sort (SSet l) -> universe "SType" l
  Sort (Prop l) -> universe "Prop" l
  Sort IntervalUniv -> return (simpleSpine "IUniv", [])
  Level l -> do
    t' <- reallyUnLevelView l
    toCSpine Nothing t' names locals
  Def q es -> do
    sym <- lift $ globalSym q
    def <- lift $ constInfo q
    -- A constructor applied to the parameters of its datatype (see
    -- "Agda.Canonical.Params").
    let sym' = case theDef def of
          ConstructorDefn{} -> sym { symSig = symDecl sym, symTy = Just (defType def) }
          _                 -> sym
    exps <- lift $ maybe (return []) (\ ty -> argTypes ty ty (appliedTerms es)) (symTy sym')
    as <- elimsToCExprAt exps es names locals
    declareDef q
    hd <- declaredName q
    applyHead hd (Just sym') (appliedTerms es) as names locals
  Con c _ es -> do
    dataname <- getConstInfo (conName c) <&> \ d -> case theDef d of
      ConstructorDefn cd -> _conData cd
      _                  -> __IMPOSSIBLE__
    as <- elimsToCExpr es names locals
    declareDef dataname
    sym <- lift $ globalSym (conName c)
    hd  <- declaredName (conName c)
    applyHead hd (Just sym) (appliedTerms es) as names locals
  Lit l -> do
    -- A natural number is unfolded into @suc (… zero)@, one constructor
    -- at a time, so that the clauses on @zero@ and @suc@ compute on it.
    mz <- getBuiltin' builtinZero
    ms <- getBuiltin' builtinSuc
    case (l, constructorForm' mz ms t) of
      (LitNat n, Just t') | n <= maxUnaryNat -> toCSpine mty t' names locals
      _ -> literalConst l
  _ -> (, []) <$> opaque (P.prettyShow t)
  where
    foreignMeta m es = do
      sym <- declareMeta m
      as  <- metaArgs m es
      applyHead (metaVarName m) sym (appliedTerms es) as names locals
    localApp m es = do
      let h = metaVarName m
      as <- metaArgs m es
      applyHead h (localSym (length names) <$> Map.lookup h locals) (appliedTerms es) as names locals
    -- The arguments of a meta are expected at the types given by its
    -- closed type, as those of a variable.
    metaArgs m es = do
      mmt  <- lift $ inferType (MetaV m [])
      exps <- lift $ maybe (return []) (\ a -> argTypes a a (appliedTerms es)) mmt
      elimsToCExprAt exps es names locals
    -- @Type@ is always declared, the other universes when needed, like it.
    universe h l = do
      declareUntyped h (snd typeSig)
      lv <- reallyUnLevelView l
      a  <- toCExpr lv names locals
      return (CSpine h [a], [])

-- | Declares the interval, and returns the names of @i0@ and @i1@.
intervalEnds :: TransM (String, String)
intervalEnds = do
  iq  <- fromMaybe __IMPOSSIBLE__ <$> getBuiltinName' builtinInterval
  i0q <- fromMaybe __IMPOSSIBLE__ <$> getBuiltinName' builtinIZero
  i1q <- fromMaybe __IMPOSSIBLE__ <$> getBuiltinName' builtinIOne
  declareDef iq
  (,) <$> declaredName i0q <*> declaredName i1q

-- | @Face φ u@ and @i½@ (see "Agda.Canonical.Cubical", constraints on a
--   face), which are not definitions of Agda.  @Face@ is declared when it
--   is first met.
auxSpine :: String -> Elims -> [String] -> Locals -> TransM (CSpine, [CDecl])
auxSpine h es names locals = do
  declared <- any ((== h) . name) <$> gets tsContext
  unless declared $ do
    (i0, i1) <- intervalEnds
    one <- fromMaybe __IMPOSSIBLE__ <$> getBuiltinName' builtinItIsOne
    declareDef one
    pushDecls =<< faceDecls i0 i1 <$> declaredName one
  case appliedTerms es of
    [phi, u] -> do
      ephi <- toCExpr phi names locals
      eu   <- etaTo 1 =<< toCExpr u names locals
      return (CSpine h [ephi, eu], [])
    _ -> return (simpleSpine h, [])

-- | 'restoreRoot' in the context of Agda, which is the one of the bound
--   names: the translation extends both together.  A context that does not
--   match (an internal error) leaves the term as it is.
restored :: Maybe Type -> Term -> [String] -> TransM Term
restored mty t names = do
  n <- getContextSize
  if n /= length names then return t else do
    (t', why) <- lift (restoreRoot mty t)
    mapM_ note why
    return t'

-- | 'inferType' in the context of Agda (see 'restored').
inferHere :: Term -> [String] -> TransM (Maybe Type)
inferHere t names = do
  n <- getContextSize
  if n /= length names then return Nothing else lift (inferType t)

-- | The type of a bound variable in the context of Agda (see 'restored').
boundType :: Int -> [String] -> TransM (Maybe Type)
boundType i names = do
  n <- getContextSize
  if n /= length names || i >= n then return Nothing else Just <$> typeOfBV i

-- | An opaque constant without type, declared if it is not yet.
opaque :: String -> TransM CSpine
opaque x = simpleSpine x <$ declareUntyped x []

-- | The type of a meta, closed over the context in which it was created,
--   with the metas solved since instantiated.  'Nothing' if it is not a
--   local meta with a type (e.g. a sort meta).
closedMetaType :: MetaId -> TCM (Maybe Type)
closedMetaType m = lookupLocalMeta' m >>= \case
  Just MetaVar{ mvJudgement = HasType{ jMetaType = a } } ->
    Just <$> instantiateFull a
  _ -> return Nothing

-- | Declares a meta that is not one of the goal, e.g. the type @?A@ of a
--   variable of the context @{a : ?A}@, as an opaque constant of its closed
--   type (Canonical cannot find it), or without type if it is not known.
--   Returns its signatures.
declareMeta :: MetaId -> TransM (Maybe Sym)
declareMeta m = do
  mty <- lift $ closedMetaType m
  msym <- lift $ forM mty $ \ a -> do
    sg <- tySig a
    return Sym { symSig = sg, symTy = Just a, symDecl = sg }
  unlessM (seenMember x <$> getSeen) $ do
    -- Declared before its type, which may mention it.
    modifySeen (seenInsert x (maybe [] symDecl msym))
    case mty of
      Just a  -> pushDecl . fst =<< inTopContext (declare Definition (unEl a) x [] [] Map.empty)
      Nothing -> pushDecl (untyped x)
  return msym
  where
    x = metaVarName m

-- | A literal that is not unfolded into constructors (a string, a
--   character, …) is declared as an opaque constant of its type, named by
--   its printed form.  It is kept undeclared if its type is unknown.
literalConst :: Literal -> TransM (CSpine, [CDecl])
literalConst l = do
  unlessM (seenMember s <$> getSeen) $ do
    mty <- lift $ (Just <$> litType l) `catchError` \ _ -> return Nothing
    whenJust mty $ \ ty -> do
      modifySeen (seenInsert s [])
      (d, _) <- inTopContext $ declare Definition (unEl ty) s [] [] Map.empty
      pushDecl d
  return (simpleSpine s, [])
  where
    s = P.prettyShow l

-- | Translates the arguments of a list of eliminations.
--
--   The application of a path to an interval term is an ordinary application
--   (see "Agda.Canonical.Cubical"), or one of @Path.f@ (see 'applyHead').
--   The projections are applications of them (see 'restoreRoot'); those
--   left (when the type of the projected term is unknown) are opaque
--   constants, named by their printed form.
elimsToCExpr :: [Elim' Term] -> [String] -> Locals -> TransM [CExpr]
elimsToCExpr = elimsToCExprAt []

-- | 'elimsToCExpr', given the types expected for the applied terms, as
--   declared and as instantiated (see 'toCExprAt' and 'argTypes').
elimsToCExprAt :: [Maybe (Type, Type)] -> [Elim' Term] -> [String] -> Locals -> TransM [CExpr]
elimsToCExprAt exps es names locals = zipWithM elim (snd (mapAccumL expect exps es)) es
  where
    -- Each applied term takes the next expected type.
    expect xs Proj{}   = (xs, Nothing)
    expect (x : xs) _  = (xs, x)
    expect []       _  = ([], Nothing)
    elim ex = \case
      Apply a      -> toCExprAt ex (unArg a) names [] locals
      IApply _ _ r -> toCExpr r names locals
      e            -> CExpr [] [] <$> opaque (P.prettyShow e)

-- | The types of the arguments of a function of type @raw@, as declared
--   (the earlier arguments are variables) and as instantiated with the
--   given arguments (in @inst@).
argTypes :: Type -> Type -> [Term] -> TCM [Maybe (Type, Type)]
argTypes _ _ [] = return []
argTypes raw inst (a : as) = do
  r <- piReduced raw
  i <- piReduced inst
  case (r, i) of
    (Pi rd rb, Pi idom ib) ->
      (Just (unDom rd, unDom idom) :) <$> argTypes (absBody rb) (absApp ib a) as
    _ -> return []
  where
    -- A type that is not a Π-type is reduced, to unfold its definition.
    piReduced t = case unEl t of
      u@Pi{} -> return u
      u      -> reduce u `catchError` \ _ -> return u

-- | The codomain of a Π-type, as the type of the body of a λ that binds no
--   variable: unknown if it depends on the variable.
noAbsBody :: Abs Type -> Maybe Type
noAbsBody = \case
  NoAbs _ t           -> Just t
  b@(Abs _ t)
    | 0 `freeIn` t    -> Nothing
    | otherwise       -> Just (absApp b __DUMMY_TERM__)

-- | Is the term a Π-type?
isPi :: Term -> Bool
isPi Pi{} = True
isPi _    = False

---------------------------------------------------------------------------
-- * Definitions
---------------------------------------------------------------------------

-- | Declares a definition (and what it depends on) to Canonical, if not
--   done yet.  The types of definitions are closed.
--
--   * A datatype comes with its constructors and its recursor.
--   * A record comes with its constructor and its projections.
--   * A function comes with its clauses, as rewrite rules.
--   * @_⊔_@ comes with 'levelMaxEqs', and @PathP@ with @Path.mk@ and @Path.f@.
declareDef :: QName -> TransM ()
declareDef q = do
  done <- Map.member q . seenCanon <$> getSeen
  unless done $ inTopContext $ do
    def <- lift $ constInfo q
    case theDef def of
      -- A constructor is declared with its datatype.
      ConstructorDefn cd -> declareDef (_conData cd)
      _ -> do
        n   <- pickName q
        sym <- lift $ globalSym q
        let dty = defType def
        modifySeen (seenInsertDef n q (symDecl sym))
        eqs <- builtinEqs q n
        (d, _) <- declare Definition (unEl dty) n eqs [] Map.empty
        declareBody q def sym d
        -- The operations with faces come with what they are written with.
        faced <- lift (hasFaces q)
        when faced $ mapM_ declareDef =<< faceSymbols

-- | Does the operation of Cubical Agda take partial elements, its faces
--   (@hcomp@, @hfill@, @comp@, @primGlue@, @prim^glue@, @prim^unglue@)?
hasFaces :: QName -> TCM Bool
hasFaces q = do
  ps <- mapM getPrimitiveName' [PrimHComp, PrimComp, PrimGlue, Prim_glue, Prim_unglue]
  return (Just q `elem` ps || nameToString q == "hfill")

-- | What the faces of an operation are written with ('hasFaces'): systems
--   (@primPOr@) and @itIsOne@.  The empty system @isOneEmpty@ is only
--   declared when the problem has an empty face ('mentionsEmptyFace'):
--   it would otherwise be a candidate for every partial element.
faceSymbols :: TransM [QName]
faceSymbols = catMaybes <$> sequence [ getPrimitiveName' PrimPOr, getBuiltinName' builtinItIsOne ]

-- | Do the terms mention the empty face: @IsOne i0@, @Partial i0 A@ or
--   @PartialP i0 A@ (e.g. the hole of @hcomp {φ = i0} ? a@)?
mentionsEmptyFace :: [Term] -> TCM Bool
mentionsEmptyFace ts = do
  isOne <- getBuiltinName' builtinIsOne
  parts <- catMaybes <$> mapM getBuiltinName' [builtinPartial, builtinPartialP]
  let phis = flip foldTerm ts $ \case
        Def q (Apply a : _)          | Just q == isOne  -> [unArg a]
        Def q (Apply _ : Apply a : _) | q `elem` parts -> [unArg a]
        _                                               -> []
  anyM (\ phi -> isZero <$> (intervalView =<< reduce phi)) phis
  where
    isZero IZero = True
    isZero _     = False

-- | The operations of Cubical Agda: @hcomp@, @hfill@, @primPOr@,
--   @transp@, @comp@ and @Glue@ (@primGlue@, @prim^glue@, @prim^unglue@).
--   As any definition, they are only declared when the problem mentions
--   them or when they are given as lemmas, and also when the hole is one
--   of their arguments (see 'Agda.Canonical.Hole.enclosingOps').
--   Those with faces come with 'faceSymbols' (see 'declareDef').
--   @hfill@ is a definition of the libraries, recognized by its name.
isCubicalOp :: QName -> TCM Bool
isCubicalOp q = do
  ps <- mapM getPrimitiveName' [PrimHComp, PrimPOr, PrimTrans, PrimComp, PrimGlue, Prim_glue, Prim_unglue]
  return (Just q `elem` ps || nameToString q == "hfill")

-- | Declares a definition, given the declaration of its type, with what
--   comes with it (see 'declareDef').
declareBody :: QName -> Definition -> Sym -> CDecl -> TransM ()
declareBody q def sym d = case theDef def of
  DatatypeDefn dd -> do
    pushDecl d
    ctors <- declareCtors (_dataCons dd)
    -- The interval cannot be eliminated.
    interval <- isInterval q
    mrec <- if interval then return Nothing else lift $ mkRecursor (_dataPars dd) d ctors
    pushDecls ctors
    declareRecursor mrec
  RecordDefn rd -> do
    pushDecl d
    ctors <- declareCtors [conName (_recConHead rd)]
    pushDecls ctors
    -- The projections, whose rules mention the constructor.
    mapM_ (declareDef . unDom) (_recFields rd)
    -- With η-equality, the projections are enough (Agda identifies @r@
    -- and @c (r .f₁) … (r .fₙ)@), and give simpler solutions than a
    -- pattern-matching λ.  Otherwise, the recursor is printed as a
    -- pattern-matching λ on the constructor, which needs a name.  A
    -- coinductive record (e.g. @∞@, @BUILTIN INFINITY@) cannot be
    -- matched on.
    let eta   = case _recEtaEquality rd of { YesEta -> True; _ -> False }
        coind = _recInduction rd == Just CoInductive
    mrec <- if _recNamedCon rd && not eta && not coind
            then lift $ mkRecursor (_recPars rd) d ctors else return Nothing
    declareRecursor mrec
  -- As in Agda, a function that fails the termination check, or an
  -- irrelevant one, is not unfolded: it has no rules.
  FunctionDefn fd -> do
    let cls | defNonterminating def || isIrrelevant def = []
            | otherwise                                 = _funClauses fd
    withClauses (droppedParams (theDef def)) cls
  -- A builtin function on natural numbers (@BUILTIN NATPLUS@, …) keeps
  -- its clauses, which Agda uses on terms that are not literals.
  PrimitiveDefn pd | not (null (_primClauses pd)) -> withClauses 0 (_primClauses pd)
  _ -> do
    pushDecl d
    -- @PathP@ comes with @Path.mk@ and @Path.f@.
    pathP <- (Just q ==) <$> getBuiltinName' builtinPathP
    cub   <- isCubical
    when (pathP && cub) $ do
      iq <- fromMaybe __IMPOSSIBLE__ <$> getBuiltinName' builtinInterval
      (i0, i1) <- intervalEnds
      iN <- declaredName iq
      pushDecls (pathDecls (name d) iN i0 i1)
      modifySeen $ \ s -> foldr (uncurry seenInsert) s pathSigs
  where
    withClauses np cls = do
      eqs <- clausesToEquations q (symDecl sym) np cls
      pushDecl d { equations = equations d ++ eqs }
    declareRecursor = flip whenJust $ \ (r, s) -> do
      pushDecl r
      modifySeen (seenInsert (name r) s)

-- | Declares constructors, and @Level@ (for the recursor).  Returns their
--   declarations, in order, which are not added to the context yet.
declareCtors :: [QName] -> TransM [CDecl]
declareCtors cs = inTopContext $ do
  syms <- lift $ mapM globalSym cs
  tys  <- lift $ mapM (fmap defType . constInfo) cs
  ns   <- forM (zip cs syms) $ \ (c, s) -> do
    n <- pickName c
    modifySeen (seenInsertDef n c (symDecl s))
    return n
  ds <- forM (zip tys ns) $ \ (t, n) -> fst <$> declare Definition (unEl t) n [] [] Map.empty
  declareDef =<< fromMaybe __IMPOSSIBLE__ <$> getName' BuiltinLevel
  return ds

-- | The names of the declarations of "Agda.Canonical.Builtin", and of the
--   symbols of Agda that they, or the rules of 'builtinEqs', mention.
reservedNames :: [String]
reservedNames =
  [ "Type", "SType", "Prop", "IUniv", "Pi", "Pi.mk", "Pi.f", "Path.mk", "Path.f", "Goal"
  , "Level", "lzero", "lsuc", "_⊔_", "primIMin", "primIMax", "primINeg" ] ++ auxNames

-- | The reserved name of a symbol of Agda that "Agda.Canonical.Builtin"
--   mentions, whatever its name in Agda.
fixedName :: HasBuiltins m => QName -> m (Maybe String)
fixedName q = do
  lv <- getName' BuiltinLevel
  lz <- getName' builtinLevelZero
  ls <- getName' builtinLevelSuc
  mx <- getName' PrimLevelMax
  ps <- mapM getPrimitiveName' [PrimIMin, PrimIMax, PrimINeg]
  return $ lookup (Just q) $
    zip [lv, lz, ls, mx] ["Level", "lzero", "lsuc", "_⊔_"] ++
    zip ps ["primIMin", "primIMax", "primINeg"]

-- | The name to declare a definition under: 'symName', with primes if it is
--   already taken (Agda names may be overloaded) or reserved.  It is
--   recorded by 'seenInsertDef'.
pickName :: QName -> TransM String
pickName q = fixedName q >>= \case
  Just n  -> return n
  Nothing -> do
    base <- symName q
    seen <- getSeen
    -- A name ending in @.rec@ (a field @rec@) would be taken for a recursor.
    let taken n = n `seenMember` seen || n `elem` reservedNames || ".rec" `isSuffixOf` n
    return $ until (not . taken) (++ "'") base

-- | The name under which a definition is declared ('pickName'); 'symName'
--   if it is not declared.
declaredName :: QName -> TransM String
declaredName q = maybe (symName q) return . Map.lookup q . seenCanon =<< getSeen

-- | The name of a definition in Agda, as declared to Canonical when it is
--   free: its unqualified name, except for a record projection, qualified
--   by its record (@R.f@), since field names are often also names of
--   variables.
symName :: HasConstInfo m => QName -> m String
symName q = getConstInfo q <&> \ d -> case theDef d of
  Function { funProjection = Right p } | Just r <- projProper p ->
    nameToString r ++ "." ++ nameToString q
  _ -> nameToString q

-- | The rules of a symbol that Agda computes with internally: @_⊔_@ on
--   levels, and in Cubical Agda the primitives on the interval, @primPOr@,
--   @IsOne1@, @IsOne2@ and @hcomp@.
builtinEqs :: QName -> String -> TransM [CEquation]
builtinEqs q n = fixedName q >>= \case
  Just "_⊔_" -> return levelMaxEqs
  Just p | p `elem` ["primIMin", "primIMax", "primINeg"] -> do
    cub <- isCubical
    if not cub then return [] else do
      (i0, i1) <- intervalEnds
      return (intervalEqs i0 i1 n)
  _ -> do
    cub <- isCubical
    if not cub then return [] else do
      por <- getPrimitiveName' PrimPOr
      hc  <- getPrimitiveName' PrimHComp
      o1  <- getBuiltinName' builtinIsOne1
      o2  <- getBuiltinName' builtinIsOne2
      let rules | Just q == por = Just porEqs
                | Just q == o1  = Just (\ i0 i1 -> isOneEqs i0 i1 True)
                | Just q == o2  = Just (\ i0 i1 -> isOneEqs i0 i1 False)
                | otherwise     = Nothing
      case rules of
        Just r  -> do
          (i0, i1) <- intervalEnds
          return (r i0 i1 n)
        Nothing | Just q == hc -> do
          (_, i1) <- intervalEnds
          hcompEqs i1 <$> itIsOneName <*> pure n
        Nothing -> do
          glues <- mapM (\ p -> (, p) <$> getPrimitiveName' p) [PrimGlue, Prim_glue, Prim_unglue]
          case lookup (Just q) glues of
            Nothing -> return []
            Just p  -> do
              (_, i1) <- intervalEnds
              one  <- itIsOneName
              -- @prim^glue@, in the rule of @prim^unglue@: an undeclared name
              -- would be a pattern variable.
              glue <- forM (fst (glues !! 1)) $ \ g -> do
                when (p == Prim_unglue) (declareDef g)
                declaredName g
              full <- if p == Prim_unglue then maybe [] pure <$> unglueFull q n else return []
              return $ maybe [] (\ g -> glueEqs i1 one g p n) glue ++ full
  where
    -- @itIsOne@, on the right-hand side of the rules.
    itIsOneName = do
      one <- fromMaybe __IMPOSSIBLE__ <$> getBuiltinName' builtinItIsOne
      declareDef one
      declaredName one

-- | The rule of @prim^unglue@ (named @n@) on the full face, as Agda computes
--   it:
--
--   > prim^unglue ℓ ℓ' A i1 T e b ⤇ equivFun (e itIsOne) b
--
--   The right-hand side is translated from Agda, in the context of the
--   variables of the rule.  'Nothing' without @equivFun@.
unglueFull :: QName -> String -> TransM (Maybe CEquation)
unglueFull q n = do
  mfun <- getTerm' builtinEquivFun
  forM mfun $ \ efun -> do
    one <- primItIsOne
    i1  <- primIOne
    t   <- defType <$> lift (constInfo q)
    -- @ℓ ℓ' A@, then @T e b@ with @φ := i1@.
    TelV tel3 r <- telViewUpTo 3 t
    TelV telR _ <- case unEl r of
      Pi _ b -> telView (absApp b i1)
      _      -> __IMPOSSIBLE__
    let tel = telFromList (telToList tel3 ++ telToList telR)
        -- @ℓ ℓ' A T e b@.
        la = var 5; lb = var 4; a = var 3; bT = var 2; e = var 1; b = var 0
        o  = setRelevance irrelevant (defaultArg one)
        rhs = efun `apply` [ setHiding Hidden (defaultArg lb), setHiding Hidden (defaultArg la)
                           , setHiding Hidden (defaultArg (bT `apply` [o])), setHiding Hidden (defaultArg a)
                           , defaultArg (e `apply` [o]), defaultArg b ]
    (_, i1n) <- intervalEnds
    termRule n tel [Right 5, Right 4, Right 3, Left (simpleExpr i1n), Right 2, Right 1, Right 0] rhs

-- | A rewrite rule @n args ⤇ rhs@, in the context of the variables of @tel@:
--   an argument is a variable (its de Bruijn index in @tel@, η-expanded) or
--   a given expression; @rhs@ is a term of Agda, translated in @tel@.
termRule :: String -> Telescope -> [Either CExpr Int] -> Term -> TransM CEquation
termRule n tel args rhs = do
  ns   <- mapM (freshString . \ x -> if x == "_" then "x" else x) (teleNames tel)
  -- The arities of the variables, of types such as @Partial φ A@ that
  -- reduce to Π-types.
  sigs <- forM (zip [0 ..] (telToList tel)) $ \ (j, d) ->
    termSig <$> (inlinePaths =<< inTopContext (addContext (telFromList (take j (telToList tel)))
                                                 (reduce (unEl (snd (unDom d))))))
  let locals = Map.fromList (zip ns (map (, Nothing) sigs))
      names  = reverse ns
  e   <- inTopContext $ addContext tel $ toCExprAt Nothing rhs names [] locals
  las <- forM args $ \case
    Left x  -> return x
    Right k -> etaVar (names !! k) (length (sigs !! (length ns - 1 - k)))
  return (CEquation (CSpine n las) (spine e) True)

-- ** Clauses

-- | Translates the clauses of a function, skipping the unsupported ones.
--
--   Agda tries the clauses in order, while Canonical's rewrite rules may
--   apply in any order: each clause only stands for the instances of its
--   patterns that no earlier clause matches (see 'disjoint').  With
--   @f 1 = 7@ and @f (suc n) = n@, the second rule is @f (suc (suc y)) ⤇ suc y@.
--
--   A clause by copatterns (@head (f x) = e@) is a rule of the projection
--   ('clauseToEquations').  It stands for the instances that no earlier
--   clause matches, like the others, and a shorter earlier clause counts:
--   @f x@ is a prefix of @head (f x)@.  In the other order (@head (f x) = e@
--   then @f x = e'@), it cannot be kept: to apply a rule of @head@, Canonical
--   first reduces its argument, so @f x ⤇ e'@ would hide the rule of @head@.
--   The later clause is then skipped.
clausesToEquations :: QName -> Sig -> Int -> [Clause] -> TransM [CEquation]
clausesToEquations q sg np cls = do
  lhss <- lift $ mapM (clauseLhs np) cls
  fmap concat $ forM (zip [0 ..] lhss) $ \ (i, (cl, ns, mps)) -> do
    let skip why = [] <$ note ("clause " ++ show (i + 1 :: Int) ++ " of " ++ P.prettyShow q
                               ++ " skipped: " ++ why)
        earlier  = [ qs | (_, _, Just qs) <- take i lhss ]
    case mps of
      Nothing -> skip "unsupported pattern"
      Just ps
        | or [ any isProjPat qs && length qs > length ps && not (clash ps qs) | qs <- earlier ] ->
            skip "it follows a clause by copatterns that overlaps it"
        | otherwise -> do
            let copat = any isProjPat ps
                -- An absurd clause, or one without rule, still comes first.
                before qs = if copat then length qs <= length ps else length qs == length ps
            pieces <- lift $ disjoint ps (filter before earlier)
            if copat && null pieces then return [] else
              fromMaybe [] <$> attempt (clauseToEquations q sg np cl ns pieces)

-- | The patterns of a clause, preceded by wildcards for the parameters
--   dropped by Agda from the clauses of a projection or of a
--   projection-like function (see "Agda.Canonical.Params"): its body does
--   not use them.  Also returns the fresh names of the variables of the
--   clause, the first one first.  'Nothing' for an unsupported pattern.
clauseLhs :: Int -> Clause -> TCM (Clause, [String], Maybe [Pat])
clauseLhs np cl = do
  ns  <- mapM freshString (teleNames (clauseTel cl))
  ws  <- replicateM np (LVar <$> freshString "p")
  mps <- mapM (patToPat (reverse ns) . namedArg) (namedClausePats cl)
  return (cl, ns, (ws ++) <$> sequence mps)

-- | Translates a clause into rewrite rules, in η-long form: one for each
--   instance of its patterns given by 'disjoint', with its substitution
--   applied to the body.
--
--   The clause is skipped (no rule) if it has no body or more patterns than
--   the signature, or if its body contains an unsolved meta or uses a
--   function that the user cannot write (see 'isAuxiliary').
--
--   The rules of a clause by copatterns are added to its outermost
--   projection ('addRules'): only the head of a rule is reduced by it, and
--   the function it mentions may be declared after the projection, since the
--   definitions of a problem can all see each other.
clauseToEquations :: QName -> Sig -> Int -> Clause -> [String] -> [([Pat], Map String Pat)]
                  -> MaybeT TransM [CEquation]
clauseToEquations q sg np cl ns pieces = do
  -- A body that is still a hole, or contains one, is not a definition yet.
  body0 <- MaybeT $ return (clauseBody cl)
  body1 <- instantiateFull body0
  aux   <- lift $ anyM isAuxiliary (namesIn body1 :: [QName])
  let tel = clauseTel cl
      copat = maybe False (any isProjPat . fst) (listToMaybe pieces)
  f0 <- lift $ declaredName q
  -- The arity of the head of the rules, and how many arguments the patterns
  -- give it (the pieces of a clause have the same shape).
  (ar, n) <- case pieces of
    (ps, _) : _ | copat -> do
      (_, as, sg') <- copatSpine (const (simpleExpr "_")) f0 sg ps
      return (length sg', length as)
    _ -> return (length sg, np + length (namedClausePats cl))
  guard (not aux && noMetas body1 && n <= ar)
  sigs <- mapM (fmap termSig . inlinePaths . unEl . snd . unDom) (telToList tel)
  let locals = Map.fromList (zip ns (map (, Nothing) sigs))
  -- The body is translated in the context of the clause, extended with the
  -- λ-binders peeled off; @Var i@ is the name at position @i@.
  (xs, bs, mty, b) <- liftTCM $ inTopContext $ addContext tel $
                        peel (ar - n) (unArg <$> clauseType cl) body1
  let k = ar - n - length xs
  -- The body is η-expanded to the arity of the symbol, through @Pi.f@ if
  -- it is a Π-type as a term (@equivFun e = fst e@), see 'fixArg'.
  e' <- lift $ inTopContext $ addContext tel $ underBinders bs (reverse ns) $ \ names -> do
          e <- toCExprAt ((\ a -> (a, a)) <$> mty) b names [] locals
          if length (params e) > k then return e else fixArg names k (unEl <$> mty) e locals
  guard (length (params e') == k)
  -- The constructors of the patterns, declared with their datatypes.
  let ctors = concat [ patCtors p | (ps, sub) <- pieces, p <- ps ++ Map.elems sub ]
  lift $ mapM_ declareDef ctors
  cnames <- Map.fromList <$> mapM (\ c -> (c,) <$> lift (declaredName c)) ctors
  let pe    = patExpr (\ c -> Map.findWithDefault (nameToString c) c cnames)
      extra = map simpleExpr (xs ++ map name (params e'))
  eqs <- forM pieces $ \ (ps, sub) -> do
    (h, l, _) <- copatSpine pe f0 sg ps
    let rhs = substExpr (Map.map pe sub) e'
    return (h, CEquation (CSpine h (l ++ extra)) (spine rhs) True)
  if not copat then return (map snd eqs) else do
    lift $ mapM_ (\ (h, e) -> addRules q h [e]) eqs
    return []

-- | The left-hand side of a rule, from the patterns of a clause of a symbol:
--   its head, the arguments, η-long, and the signature of this head.  A
--   projection takes what precedes it as its record, after wildcards for the
--   parameters of the record: @f x .head y@ is @head p (f x) y@.  It fails
--   if the symbol does not have exactly the arguments before the projection.
copatSpine :: (Pat -> CExpr) -> String -> Sig -> [Pat] -> MaybeT TransM (String, [CExpr], Sig)
copatSpine pe = go []
  where
    go done h sg ps = do
      let (pre, post) = break isProjPat ps
          n           = length done + length pre
      guard (n <= length sg)
      as <- zipWithM etaTo (map pArity (drop (length done) sg)) (map pe pre)
      let args = done ++ as
      case post of
        LProj r : rest -> do
          guard (n == length sg)
          pars <- MaybeT $ lift (projParams r)
          lift $ declareDef r
          ws <- lift $ replicateM pars (simpleExpr <$> freshString "p")
          h' <- lift $ declaredName r
          sg' <- lift $ lift $ symDecl <$> globalSym r
          go (ws ++ [CExpr [] [] (CSpine h args)]) h' sg' rest
        _ -> return (h, args, sg)

-- | Number of parameters of the record of a projection.
projParams :: QName -> TCM (Maybe Int)
projParams r = theDef <$> getConstInfo r <&> \case
  Function { funProjection = Right p } | Just _ <- projProper p, projIndex p > 0 ->
    Just (projIndex p - 1)
  _ -> Nothing

-- | Adds rules to a declaration already in the context.  The projection of a
--   record whose field types mention the function is not there yet: the
--   rules are then lost, which only leaves the function not unfolded.
addRules :: QName -> String -> [CEquation] -> TransM ()
addRules q h eqs = do
  ctx <- gets tsContext
  if any ((== h) . name) ctx
    then modify $ \ s -> s { tsContext =
           [ if name d == h then d { equations = equations d ++ eqs } else d | d <- ctx ] }
    else note ("a clause of " ++ P.prettyShow q ++ " skipped: " ++ h ++ " is being declared")

-- | @peel k mty t@ removes up to @k@ λ-binders of @t@, of type @mty@ if
--   known, with fresh names.  Returns these names, the binders that bind a
--   variable with their types (see 'underBinders'), the type of the body if
--   known, and the body.
peel :: Int -> Maybe Type -> Term -> TCM ([String], [(String, Dom Type)], Maybe Type, Term)
peel k mty (Lam _ b) | k > 0 = do
  x <- freshString (absName b)
  mpi <- case mty of
    Just a -> reduce (unEl a) <&> \case
      Pi dom cod -> Just (dom, cod)
      _          -> Nothing
    Nothing -> return Nothing
  let dom = maybe (defaultDom __DUMMY_TYPE__) fst mpi
      (bs, mty') = case b of
        Abs{}   -> ([(x, dom)], absBody . snd <$> mpi)
        NoAbs{} -> ([], noAbsBody . snd =<< mpi)
  (xs, bs', mty'', t) <- addContext bs $ peel (k - 1) mty' (unAbs b)
  return (x : xs, bs ++ bs', mty'', t)
peel _ mty t = return ([], [], mty, t)

-- | A pattern-matching lambda or the auxiliary function of a @with@: their
--   names cannot be written in Agda, so a solution must not unfold to them.
isAuxiliary :: QName -> TransM Bool
isAuxiliary q = getConstInfo q <&> \ d -> case theDef d of
  Function { funExtLam = Just _ } -> True
  Function { funWith = WithFunction{} } -> True
  _                               -> False
