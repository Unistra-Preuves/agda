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
--   * __Partial elements.__  @Partial φ A@ is the Π-type @IsOne φ → A@.
--     @primPOr@ comes with its computation rules ('porEqs'), and @IsOne1@
--     and @IsOne2@ with those that type them ('isOneEqs'), @hcomp@ with
--     its rule on the full face ('hcompEqs').
--
--   * __Glue.__  @primGlue@, @prim^glue@ and @prim^unglue@ come with their
--     rules on the full face, and @unglue (glue t a) ⤇ a@ ('glueEqs').
--
--   * __Constraints on a face.__  A constraint @φ ⊢ u = v@ of Agda, on a
--     face @φ@ that is a meta, is stated as equations under a symbol
--     @Face@ that compares @u@ and @v@ only when @φ@ is @i1@ ('faceDecls').
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
  , porEqs, isOneEqs
  , hcompEqs
  , glueEqs
  , isPartial
  , faceQName, halfQName, auxName, faceTerm, halfTerm
  , halfDecl, faceDecls, auxNames
  , pathDecls, pathSigs
  , anySort
  ) where

import Data.Maybe (isJust)
import Data.Word (Word64)

import Agda.Canonical.Types
import Agda.Syntax.Abstract.Name (makeName, qualify_)
import Agda.Syntax.Concrete.Name qualified as C
import Agda.Syntax.Builtin
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Position (noRange)
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Pure (PureTCM)
import Agda.TypeChecking.Free (freeIn)
import Agda.TypeChecking.Reduce (reduce)
import Agda.TypeChecking.Substitute

---------------------------------------------------------------------------
-- * Mode
---------------------------------------------------------------------------

-- | Does the current file use Cubical Agda?
isCubical :: HasOptions m => m Bool
isCubical = isJust <$> cubicalOption

-- | Is the name the interval @I@?
isInterval :: HasBuiltins m => QName -> m Bool
isInterval q = (Just q ==) <$> getBuiltinName' builtinInterval

---------------------------------------------------------------------------
-- * Paths as functions
---------------------------------------------------------------------------

-- | The sort given to the types built here.  It only matters for a Π-type
--   occurring as a term, and the types built here occur in type positions.
anySort :: Sort
anySort = mkType 0

-- | The path type at the end of a type, after its Π-binders.
pathCodomain :: PureTCM m => Term -> m (Maybe (Arg Term, Arg Term, Arg Term))
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
inlinePaths :: PureTCM m => Term -> m Term
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
pathEnds :: PureTCM m => Term -> m (Maybe (Int, Term, Term))
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
commutePath :: PureTCM m => Term -> m (Maybe Term)
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
iunivDecl = untyped "IUniv"

-- | The rules of a primitive on the interval, given the names of @i0@ and
--   @i1@: the computation rules of @_∧_@ and @_∨_@ (as for booleans), and
--   the De Morgan laws and involution for @~_@.
--
--   They also compute on the point @i½@ of 'halfDecl' (@i½ ∧ i½ ⤇ i½@,
--   @~ i½ ⤇ i½@), the others coming from those on @i0@ and @i1@.
--
--   There is no idempotence rule (@i ∧ i ⤇ i@): Canonical does not apply
--   a symbol with a non-linear rule.
intervalEqs :: String -> String -> String -> [CEquation]
intervalEqs i0 i1 p = map (ruleVars ["i", "j"]) $ case p of
  "primIMin" ->
    [ eq (app2 p (e halfName) (e halfName)) (s halfName)
    , eq (app2 p (e i0) j) (s i0), eq (app2 p (e i1) j) (s "j")
    , eq (app2 p i (e i0)) (s i0), eq (app2 p i (e i1)) (s "i") ]
  "primIMax" ->
    [ eq (app2 p (e halfName) (e halfName)) (s halfName)
    , eq (app2 p (e i0) j) (s "j"), eq (app2 p (e i1) j) (s i1)
    , eq (app2 p i (e i0)) (s "i"), eq (app2 p i (e i1)) (s i1) ]
  "primINeg" ->
    [ eq (CSpine p [e i0]) (s i1), eq (CSpine p [e i1]) (s i0), eq (CSpine p [e halfName]) (s halfName)
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
-- * Partial elements
---------------------------------------------------------------------------

-- | The rules of @primPOr@, given the names of @i0@ and @i1@, and its name:
--
--   > primPOr : ∀ {ℓ} (i j : I) {A : Partial (i ∨ j) (Set ℓ)}
--   >           (u : PartialP i (λ o → A (IsOne1 i j o)))
--   >           (v : PartialP j (λ o → A (IsOne2 i j o))) → PartialP (i ∨ j) A
--   >
--   > primPOr ℓ i1 j A u v o ⤇ u o        primPOr ℓ i i1 A u v o ⤇ v o
--   > primPOr ℓ i0 j A u v o ⤇ v o        primPOr ℓ i i0 A u v o ⤇ u o
--
--   as Agda computes it.  The rules overlap when @i@ and @j@ are both
--   @i0@ or @i1@: @u@ and @v@ then agree for Agda, or there is no @o@.
porEqs :: String -> String -> String -> [CEquation]
porEqs i0 i1 p = map (ruleVars ["ℓ", "i", "j", "A", "u", "v", "o", "z"])
  [ rule (e i1) j "u", rule (e i0) j "v", rule i (e i1) "v", rule i (e i0) "u" ]
  where
    e      = simpleExpr
    i      = e "i"
    j      = e "j"
    rule a b w = CEquation
      (CSpine p [e "ℓ", a, b, eta1 "A", eta1 "u", eta1 "v", e "o"])
      (CSpine w [e "o"]) True
    -- @λ z. n z@
    eta1 n = CExpr [untyped "z"] [] (CSpine n [simpleExpr "z"])

-- | The rules of @IsOne1@ (@isOne1 = True@) or @IsOne2@, given the names
--   of @i0@ and @i1@, and its name: when @i ∨ j@ reduces to the side it
--   comes from, the proof is that of the side.
--
--   > IsOne1 i1 j z ⤇ z        IsOne1 i i0 z ⤇ z
--   > IsOne2 i0 j z ⤇ z        IsOne2 i i1 z ⤇ z
--
--   They type the rules of 'porEqs': there, @u o : A (IsOne1 i1 j o)@ must
--   have the type @A o@.  (Agda identifies all the proofs of @IsOne φ@.)
isOneEqs :: String -> String -> Bool -> String -> [CEquation]
isOneEqs i0 i1 isOne1 p = map (ruleVars ["i", "j", "z"]) $
  if isOne1 then [rule (e i1) j, rule i (e i0)]
            else [rule (e i0) j, rule i (e i1)]
  where
    e        = simpleExpr
    i        = e "i"
    j        = e "j"
    rule a b = CEquation (CSpine p [a, b, e "z"]) (simpleSpine "z") True

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
    eta1 n = CExpr [untyped "z"] [] (CSpine n [simpleExpr "z"])

-- | Signatures of 'pathDecls', all parameters explicit.
pathSigs :: [(String, Sig)]
pathSigs = [("Path.mk", base ++ [p 1]), ("Path.f", base ++ [p 0, p 0])]
  where
    p n  = Param n NotHidden
    base = [p 0, p 1, p 0, p 0]

-- | The rule of @hcomp@ on the full face, given the names of @i1@ and
--   @itIsOne@, and its name:
--
--   > hcomp : ∀ {ℓ} {A : Set ℓ} {φ : I} (u : ∀ i → Partial φ A) (a : A) → A
--   >
--   > hcomp ℓ A i1 u a ⤇ u i1 itIsOne
--
--   Its other rules, by the type @A@, are left out.
hcompEqs :: String -> String -> String -> [CEquation]
hcompEqs i1 one p = map (ruleVars ["ℓ", "A", "u", "a", "j", "o"])
  [ CEquation (CSpine p [e "ℓ", e "A", e i1, eta2 "u", e "a"])
              (CSpine "u" [e i1, e one]) True ]
  where
    e = simpleExpr
    -- @λ j o. n j o@
    eta2 n = CExpr [untyped "j", untyped "o"] [] (CSpine n [e "j", e "o"])

-- | The rules of @primGlue@, @prim^glue@ and @prim^unglue@ (given by
--   'PrimitiveId'), given the names of @i1@, @itIsOne@ and @prim^glue@, and
--   the name of the primitive, but the rule of @prim^unglue@ on the full
--   face, whose right-hand side is a term of Agda (see
--   'Agda.Canonical.ToCanonical.builtinEqs'):
--
--   > primGlue ℓ ℓ' A i1 T e ⤇ T itIsOne
--   > prim^glue ℓ ℓ' A i1 T e t a ⤇ t itIsOne
--   > prim^unglue ℓ ℓ' A φ T e (prim^glue _ _ _ _ _ _ t a) ⤇ a
--
--   The arguments of @prim^glue@ are wildcards, so that the rule is linear.
glueEqs :: String -> String -> String -> PrimitiveId -> String -> [CEquation]
glueEqs i1 one glue prim p = map (ruleVars vs) $ case prim of
  PrimGlue    -> [ CEquation (CSpine p (hd (e i1))) (CSpine "T" [e one]) True ]
  Prim_glue   -> [ CEquation (CSpine p (hd (e i1) ++ [eta1 "t", e "a"])) (CSpine "t" [e one]) True ]
  Prim_unglue -> [ CEquation (CSpine p (hd (e "φ") ++ [glued])) (simpleSpine "a") True ]
  _           -> []
  where
    vs = ["ℓ", "ℓ'", "A", "φ", "T", "e", "t", "a", "b", "z", "ℓ2", "ℓ2'", "A2", "φ2", "T2", "e2"]
    e  = simpleExpr
    hd f = [e "ℓ", e "ℓ'", e "A", f, eta1 "T", eta1 "e"]
    glued = CExpr [] [] $ CSpine glue
      [e "ℓ2", e "ℓ2'", e "A2", e "φ2", eta1 "T2", eta1 "e2", eta1 "t", e "a"]
    -- @λ z. n z@
    eta1 n = CExpr [untyped "z"] [] (CSpine n [e "z"])

-- | Is the type @Partial φ A@ or @PartialP φ A@, a Π-type over @IsOne φ@
--   whatever its arguments?
isPartial :: HasBuiltins m => Term -> m Bool
isPartial (Def q _) = do
  ps <- mapM getBuiltinName' [builtinPartial, builtinPartialP]
  return (Just q `elem` ps)
isPartial _ = return False

---------------------------------------------------------------------------
-- * Constraints on a face
---------------------------------------------------------------------------

-- $face
-- Agda keeps a constraint @φ ⊢ u = v@ between partial elements @u v :
-- (o : IsOne φ) → B o@ when @φ@ is blocked, e.g. on a meta that Canonical
-- finds (the face of an @hcomp@ whose sides are a hole).  It holds when @u@
-- and @v@ are equal on each face of @φ@, a conjunction of @i = i0@ and @i
-- = i1@.  Canonical has no conditional equation; the constraint is stated,
-- for each assignment @ρ@ of the interval variables of @φ@ to @i0@, @i1@,
-- or none (@3ⁿ@ of them), as
--
-- > Face φ[ρ, ½] uρ ⤇ Face φ[ρ, ½] vρ
--
-- where @φ[ρ, ½]@ is @φρ@ with its other variables set to the point @i½@.
-- Once @φ@ is found, it reduces to @i0@, @i1@ or @i½@: a term of the
-- interval without @i0@ and @i1@ is @i½@ there, and the rules of @_∧_@,
-- @_∨_@ and @~_@ remove the constants.  So @φ[ρ, ½]@ is @i1@ exactly when
-- @φρ@ is @i1@, i.e. when @ρ@ is under a face of @φ@ (all its faces are
-- such assignments), and only then are @uρ@ and @vρ@ compared:
--
-- > Face i1 f ⤇ f itIsOne        Face i0 f ⤇ Face.tt        Face i½ f ⤇ Face.tt
--
-- @Face@, @Face.tt@ and @i½@ have no type: they are not candidates of the
-- search.  In the terms of Agda, @Face@ and @i½@ are 'faceQName' and
-- 'halfQName', which do not name definitions.

-- | The names of 'faceQName' and 'halfQName' in Canonical, and the constant
--   of 'faceDecls'.
faceName, halfName, faceTT :: String
faceName = "Face"
halfName = "i½"
faceTT   = "Face.tt"

-- | Names that stand in terms of Agda for @Face@ and @i½@, and are not
--   names of definitions.
faceQName, halfQName :: QName
faceQName = auxQName 0 faceName
halfQName = auxQName 1 halfName

auxQName :: Word64 -> String -> QName
auxQName k s = qualify_ $
  makeName (NameId (maxBound - k) (ModuleNameHash 0)) (C.simpleName s) noRange noFixity' False

-- | The name in Canonical of 'faceQName' or 'halfQName'.
auxName :: QName -> Maybe String
auxName q = lookup q [(faceQName, faceName), (halfQName, halfName)]

-- | The names declared here, reserved.
auxNames :: [String]
auxNames = [faceName, halfName, faceTT]

-- | @Face φ u@ in the terms of Agda.
faceTerm :: Term -> Term -> Term
faceTerm phi u = Def faceQName [Apply (defaultArg phi), Apply (defaultArg u)]

-- | @i½@ in the terms of Agda.
halfTerm :: Term
halfTerm = Def halfQName []

-- | The point @i½@ of the interval, without type.
halfDecl :: CDecl
halfDecl = untyped halfName

-- | @Face@ and @Face.tt@, the most recent first, given the names of @i0@,
--   @i1@ and @itIsOne@.
faceDecls :: String -> String -> String -> [CDecl]
faceDecls i0 i1 one =
  [ (untyped faceName) { equations = map (ruleVars ["f", "z"])
      [ CEquation (CSpine faceName [simpleExpr i1, eta1]) (CSpine "f" [simpleExpr one]) True
      , CEquation (CSpine faceName [simpleExpr i0, eta1]) (simpleSpine faceTT) True
      , CEquation (CSpine faceName [simpleExpr halfName, eta1]) (simpleSpine faceTT) True ] }
  , untyped faceTT ]
  where
    -- @λ z. f z@
    eta1 = CExpr [untyped "z"] [] (CSpine "f" [simpleExpr "z"])
