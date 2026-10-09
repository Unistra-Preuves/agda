-- | Cubical Agda for Canonical.
--
--   Canonical knows nothing about the interval nor about paths.  When the
--   file uses @--cubical@, the translation ("Agda.Canonical.ToCanonical")
--   therefore applies the following transformations:
--
--   * __Paths are functions from the interval.__  In a type position, a path
--     type @PathP A x y@ (or @x ≡ y@, which reduces to it) becomes
--     @(i : I) → A i@ ('inlinePaths').  A declaration of such a type, say
--     @p : Δ → PathP A x y@, comes with its boundary ('pathEnds'):
--
--     > p δ i0 ⤇ x        p δ i1 ⤇ y
--
--     as rewrite rules for the context and the definitions, as constraints
--     for a parameter.  The application of a path @p i@ is an ordinary
--     application.
--
--   * __The interval.__  @IUniv@, @I@, @i0@, @i1@ are declared (@I@ without
--     recursor: the interval cannot be eliminated), and @_∧_@, @_∨_@, @~_@
--     with their computation rules and De Morgan laws ('intervalEqs').
--
--   * __Paths as terms.__  A path type occurring as a term, e.g. as the
--     argument of a datatype, is kept as @PathP@; its values are built and
--     applied with @Path.mk@ and @Path.f@ ('pathDecls'), as Π-types with
--     @Pi.mk@ and @Pi.f@.
--
--   * __The boundary of the goal.__  In @f p i = ?@, the hole must be equal
--     to given terms when @i = i0@ and @i = i1@.  The context is refolded
--     into the type of the goal from the first constrained interval
--     variable, which becomes a path type again (see
--     'Agda.Canonical.ToCanonical.refoldBoundary').

module Agda.Canonical.Cubical
  ( isCubical
  , isInterval
  , inlinePaths, pathEnds
  , commutePath
  , iunivDecl
  , intervalEqs
  , pathDecls, pathSigs
  ) where

import Data.Maybe (isJust)

import Agda.Canonical.Types
import Agda.Syntax.Builtin
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Free (freeIn)
import Agda.TypeChecking.Reduce (reduce)
import Agda.TypeChecking.Substitute

---------------------------------------------------------------------------
-- * Mode
---------------------------------------------------------------------------

-- | Does the current file use Cubical Agda?
isCubical :: TCM Bool
isCubical = isJust <$> cubicalOption

-- | Is the name the interval @I@?
isInterval :: QName -> TCM Bool
isInterval q = (Just q ==) <$> getBuiltinName' builtinInterval

---------------------------------------------------------------------------
-- * Paths as functions
---------------------------------------------------------------------------

-- | The sort given to the types built here.  It only matters for a Π-type
--   occurring as a term, and the types built here occur in type positions.
anySort :: Sort
anySort = mkType 0

-- | The path type at the end of a type, after its Π-binders.
pathCodomain :: Term -> TCM (Maybe (Arg Term, Arg Term, Arg Term))
pathCodomain t = do
  t' <- reduce t
  pv <- pathView (El anySort t')
  return $ case pv of
    PathType { pathType = a, pathLhs = x, pathRhs = y } -> Just (a, x, y)
    OType{}                                             -> Nothing

-- | Replaces, in a type position, each path type @PathP A x y@ by
--   @(i : I) → A i@.  The domains and the codomains of Π-types are type
--   positions; the arguments of a type are not.  Identity outside of
--   Cubical Agda.
inlinePaths :: Term -> TCM Term
inlinePaths t0 = do
  cub <- isCubical
  if not cub then return t0 else do
    mi <- getBuiltinName' builtinInterval
    case mi of
      Nothing -> return t0
      Just iq -> go (El intervalSort (Def iq [])) t0
  where
    go iTy t = case t of
      Pi a b -> Pi <$> traverse (goT iTy) a <*> traverse (goT iTy) b
      _ -> pathCodomain t >>= \case
        Nothing        -> return t
        Just (a, _, _) -> do
          -- @A@ is a family @λ i → A i@: apply it to the new variable.
          body <- go iTy (raise 1 (unArg a) `apply` [defaultArg (var 0)])
          return $ Pi (defaultDom iTy) (Abs "i" (El anySort body))
    goT iTy (El s u) = El s <$> go iTy u

-- | @pathEnds t@, for @t = Δ → PathP A x y@: the length of @Δ@, and @x@ and
--   @y@ in the context of @Δ@.  'Nothing' outside of Cubical Agda.
pathEnds :: Term -> TCM (Maybe (Int, Term, Term))
pathEnds t0 = do
  cub <- isCubical
  if not cub then return Nothing else go 0 t0
  where
    go n (Pi _ b) = go (n + 1) (unEl (unAbs b))
    go n t        = fmap (\ (_, x, y) -> (n, unArg x, unArg y)) <$> pathCodomain t

-- | A path of functions is a function to paths, and a path of paths (a
--   square) is a path to paths:
--
--   > PathP (λ i → (a : A) → B i a) f g          ↦  (a : A) → PathP (λ i → B i a) (f a) (g a)
--   > PathP (λ i → PathP (λ j → B i j) _ _) l r  ↦  (j : I) → PathP (λ i → B i j) (l j) (r j)
--
--   when @A@ does not depend on @i@.  The boundary in @i@ is then closed:
--   @g i0 ≡ f a@ does not bind @a@, while @g i0 a ≡ f a@ does.  (The
--   boundary in @j@ of a square is left to Agda.)  The solution
--   @λ a i → b@ is turned back into @λ i a → b@.
commutePath :: Term -> TCM (Maybe Term)
commutePath t = do
  mp <- getBuiltinName' builtinPathP
  mi <- getBuiltinName' builtinInterval
  t' <- reduce t
  pv <- pathView (El anySort t')
  case (mp, mi, pv) of
    (Just pathP, Just iq, PathType { pathLevel = l, pathType = a, pathLhs = x, pathRhs = y }) ->
      reduce (unArg a) >>= \case
        Lam _ b -> do
          -- The family @λ i → F@, with @F@ in context @Γ, i@.
          let (i, fam) = case b of
                Abs m u   -> (m, u)
                NoAbs m u -> (m, raise 1 u)
              -- @Γ, i@ to @Γ, a, i@.
              under    = applySubst (var 0 :# raiseS 2)
              path d n body' app = Just $ Pi d $ Abs n $ El anySort $ Def pathP
                [ Apply (raise 1 l)
                , Apply (defaultArg (Lam defaultArgInfo (Abs i body')))
                , Apply (defaultArg (app x)), Apply (defaultArg (app y)) ]
          famR <- reduce fam
          pv2  <- pathView (El anySort famR)
          return $ case (famR, pv2) of
            (Pi dom c, _) | not (0 `freeIn` dom) ->
              let (n, body) = case c of
                    Abs m u   -> (m, unEl u)
                    NoAbs m u -> (m, raise 1 (unEl u))
                  -- @body@ is in context @Γ, i, a@; swap @i@ and @a@.
                  body' = applySubst (var 1 :# (var 0 :# raiseS 2)) body
                  app u = raise 1 (unArg u) `apply` [Arg (domInfo dom) (var 0)]
              in path (absApp (Abs i dom) __DUMMY_TERM__) n body' app
            (_, PathType { pathType = f2 }) ->
              let body' = under (unArg f2) `apply` [defaultArg (var 1)]
                  app u = raise 1 (unArg u) `applyE` [IApply __DUMMY_TERM__ __DUMMY_TERM__ (var 0)]
              in path (defaultDom (El intervalSort (Def iq []))) "j" body' app
            _ -> Nothing
        _ -> return Nothing
    _ -> return Nothing

---------------------------------------------------------------------------
-- * The interval
---------------------------------------------------------------------------

-- | The universe of the interval, left untyped like @Type@.
iunivDecl :: CDecl
iunivDecl = CDecl "IUniv" Nothing []

-- | The rules of a primitive on the interval, given the names of @i0@ and
--   @i1@: the computation rules of @_∧_@ and @_∨_@ (as for booleans), and
--   the De Morgan laws and involution for @~_@.
--
--   There is no idempotence rule (@i ∧ i ⤇ i@): Canonical does not apply
--   a symbol with a non-linear rule.
intervalEqs :: String -> String -> String -> [CEquation]
intervalEqs i0 i1 p = map (ruleVars ["i", "j"]) $ case p of
  "primIMin" ->
    [ eq (app2 p (e i0) j) (s i0), eq (app2 p (e i1) j) (s "j")
    , eq (app2 p i (e i0)) (s i0), eq (app2 p i (e i1)) (s "i") ]
  "primIMax" ->
    [ eq (app2 p (e i0) j) (s "j"), eq (app2 p (e i1) j) (s i1)
    , eq (app2 p i (e i0)) (s "i"), eq (app2 p i (e i1)) (s i1) ]
  "primINeg" ->
    [ eq (CSpine p [e i0]) (s i1), eq (CSpine p [e i1]) (s i0)
    , eq (CSpine p [ex (app2 "primIMin" i j)]) (app2 "primIMax" (ex (neg i)) (ex (neg j)))
    , eq (CSpine p [ex (app2 "primIMax" i j)]) (app2 "primIMin" (ex (neg i)) (ex (neg j)))
    , eq (CSpine p [ex (neg i)]) (s "i") ]
  _ -> []
  where
    eq l r     = CEquation l r True
    e          = simpleExpr
    s          = simpleSpine
    ex         = CExpr [] []
    i          = e "i"
    j          = e "j"
    app2 f a b = CSpine f [a, b]
    neg a      = CSpine "primINeg" [a]

---------------------------------------------------------------------------
-- * Paths as terms
---------------------------------------------------------------------------

-- | Declarations of @Path.mk@ and @Path.f@, given the names of @PathP@,
--   @I@, @i0@ and @i1@:
--
--   > Path.mk : (ℓ : Level) (A : I → Type ℓ) (x : A i0) (y : A i1)
--   >           (f : (i : I) → A i) {f i0 ⤇ x ; f i1 ⤇ y} → PathP ℓ A x y
--   > Path.f  : (ℓ : Level) (A : I → Type ℓ) (x : A i0) (y : A i1)
--   >           (p : PathP ℓ A x y) (i : I) → A i
--   > Path.f ℓ A x y (Path.mk _ _ _ _ f) i ⤇ f i
--   > Path.f ℓ A x y p i0 ⤇ x
--   > Path.f ℓ A x y p i1 ⤇ y
pathDecls :: String -> String -> String -> String -> [CDecl]
pathDecls pathP iN i0 i1 =
  [ CDecl "Path.mk" (Just $ CExpr (hdr ++ [CDecl "f" (Just fnT) [ CEquation (CSpine "f" [simpleExpr i0]) (simpleSpine "x") True
                                                                , CEquation (CSpine "f" [simpleExpr i1]) (simpleSpine "y") True ]])
                                  [] (CSpine pathP hd)) []
  , CDecl "Path.f"
      (Just $ CExpr (hdr ++ [typed "p" (CExpr [] [] (CSpine pathP hd)), typed "i" (simpleExpr iN)]) []
                    (CSpine "A" [simpleExpr "i"]))
      (map (ruleVars ["ℓ", "A", "x", "y", "ℓ'", "A'", "x'", "y'", "f", "p", "i", "z"])
      -- The arguments of @Path.mk@ are wildcards, so that the rule is linear.
      [ CEquation (CSpine "Path.f" (hd ++ [ CExpr [] [] (CSpine "Path.mk" (hd' ++ [eta1 "f"])), simpleExpr "i" ]))
                  (CSpine "f" [simpleExpr "i"]) True
      , CEquation (CSpine "Path.f" (hd ++ [simpleExpr "p", simpleExpr i0])) (simpleSpine "x") True
      , CEquation (CSpine "Path.f" (hd ++ [simpleExpr "p", simpleExpr i1])) (simpleSpine "y") True ])
  ]
  where
    hd   = [simpleExpr "ℓ", eta1 "A", simpleExpr "x", simpleExpr "y"]
    hd'  = [simpleExpr "ℓ'", eta1 "A'", simpleExpr "x'", simpleExpr "y'"]
    hdr  = [ typed "ℓ" (simpleExpr "Level")
           , typed "A" (CExpr [typed "j" (simpleExpr iN)] [] (CSpine "Type" [simpleExpr "ℓ"]))
           , typed "x" (CExpr [] [] (CSpine "A" [simpleExpr i0]))
           , typed "y" (CExpr [] [] (CSpine "A" [simpleExpr i1])) ]
    fnT  = CExpr [typed "i" (simpleExpr iN)] [] (CSpine "A" [simpleExpr "i"])
    -- @λ z. n z@
    eta1 n = CExpr [CDecl "z" Nothing []] [] (CSpine n [simpleExpr "z"])

-- | Signatures of 'pathDecls', all parameters explicit.
pathSigs :: [(String, Sig)]
pathSigs = [("Path.mk", base ++ [p 1]), ("Path.f", base ++ [p 0, p 0])]
  where
    p n  = Param n NotHidden
    base = [p 0, p 1, p 0, p 0]
