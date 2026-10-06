-- | Translation of an Agda goal into a Canonical problem.
--
--   The goal becomes a declaration named @Goal@ whose 'lets' contain
--   everything Canonical may use: the context variables, the lemmas given
--   by the user, and every datatype, constructor and function met while
--   translating them (with their clauses as rewrite rules and a generated
--   recursor for datatypes, see "Agda.Canonical.Recursor").
--
--   The translation functions thread the following state:
--
--   * the bound names @[String]@, the most recent first, so that the
--     de Bruijn index @i@ is the name at position @i@;
--
--   * the context @[CDecl]@ being built, the most recent declaration first
--     (it is reversed once, at the top level);
--
--   * the symbols already declared ('Seen'), to declare each symbol once and
--     to stop the recursion on recursive definitions;
--
--   * the signatures of the local variables (@Map String Sig@), used to
--     η-expand their arguments.
--
--   Canonical has no universe-polymorphic Π-type: a Π-type occurring as a
--   term is encoded with @Pi@, @Pi.mk@ and @Pi.f@ (see "Agda.Canonical.Builtin").

module Agda.Canonical.ToCanonical
  ( produceCanonicalGoal
  ) where

import Control.Monad (foldM, replicateM, zipWithM)
import Data.Foldable (foldlM)
import Data.Map (Map, insert, member)
import Data.Map qualified as Map

import Agda.Canonical.Builtin
import Agda.Canonical.Recursor (mkRecursor)
import Agda.Canonical.Types
import Agda.Canonical.Utils
import Agda.Syntax.Builtin
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty qualified as P
import Agda.Syntax.Internal
import Agda.Syntax.Internal.MetaVars (noMetas)
import Agda.Syntax.Internal.Names (namesIn)
import Agda.TypeChecking.Level (reallyUnLevelView)
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Context (underAbstraction)
import Agda.TypeChecking.Monad.Signature (HasConstInfo (getConstInfo))
import Agda.TypeChecking.Reduce (instantiateFull)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope (teleNames, telView)
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Maybe (fromMaybe)
import Agda.Utils.Size (size)

---------------------------------------------------------------------------
-- * Goal
---------------------------------------------------------------------------

-- | The Canonical problem for a goal, and what is needed to print the answer.
--
--   The lemmas are declared before the context variables, the hypotheses
--   after them.
produceCanonicalGoal
  :: [QName]                      -- ^ Lemmas given by the user.
  -> Telescope                    -- ^ Context of the goal.
  -> [(String, Type)]             -- ^ Hypotheses, with their types in that context.
  -> Type                         -- ^ Type of the goal, in that context.
  -> [([(Term, Bool)], Term)]     -- ^ Cubical boundary of the goal (currently unused).
  -> TCM (CDecl, GoalInfo)
produceCanonicalGoal lemmas ctx hyps ty _bds = do
  (lets0, ald0) <- foldlM (\ (l, a) q -> gatherDatatypeInformations q [] l a)
                          ([typeDecl], Map.fromList [typeSig]) lemmas
  aux ctx ty [] lets0 ald0 mempty
  where
    aux :: Telescope -> Type -> [String] -> [CDecl] -> Seen -> Map String Sig
        -> TCM (CDecl, GoalInfo)
    aux tel t bindnames lets ald art =
      case tel of
        EmptyTel -> do
          (lets1, ald1, art1) <- foldlM (\ (l, a, r) (n, h) -> do
                                    (d, l', a', r') <- toCDecl (unEl h) n [] bindnames l a False r
                                    return (d : l', a', r'))
                                  (lets, ald, art) hyps
          (res, _, ald', art') <- toCDecl (unEl t) "Goal" [] bindnames lets1 ald1 True art1
          return (res, GoalInfo ald' art' bindnames [] mempty)
        ExtendTel dom (Abs nb b) ->
          case unEl t of
            Pi _ codom -> do
              (domdecl, lets', ald', art') <- toCDecl (unEl $ unDom dom) nb [] bindnames lets ald False art
              aux b (unAbs codom) (nb : bindnames) (domdecl : lets') ald' art'
            _ -> __IMPOSSIBLE__
        _ -> __IMPOSSIBLE__

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

-- | A local variable: both signatures agree, its type is unknown.
localSym :: Sig -> Sym
localSym s = Sym s Nothing s

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
  TelV tel _ <- telView t
  go tel
  where
    go :: Telescope -> TCM Sig
    go EmptyTel = return []
    go (ExtendTel dom b) = do
      TelV d _ <- telView (unDom dom)
      rest <- underAbstraction dom b go
      return (Param (size d) (getHiding dom) : rest)

-- | Signatures of a definition or a constructor.
globalSym :: QName -> TCM Sym
globalSym q = do
  def <- getConstInfo q
  sg  <- tySig (defType def)
  return $ case theDef def of
    ConstructorDefn cd -> Sym (drop (_conPars cd) sg) Nothing sg
    _                  -> Sym sg (Just (defType def)) sg

---------------------------------------------------------------------------
-- * Π-types as terms
---------------------------------------------------------------------------

-- | Declares @Pi@, and @Level@ and @_⊔_@ on which it depends, if not done yet.
withPi :: [CDecl] -> Seen -> TCM ([CDecl], Seen)
withPi lets ald
  | "Pi" `member` ald = return (lets, ald)
  | otherwise = do
      lq <- fromMaybe __IMPOSSIBLE__ <$> getName' BuiltinLevel
      mq <- fromMaybe __IMPOSSIBLE__ <$> getName' PrimLevelMax
      let ald0 = foldr (uncurry insert) ald piSigs
      (lets1, ald1) <- foldlM (\ (l, a) q -> gatherDatatypeInformations q [] l a)
                              (lets, ald0) [lq, mq]
      return (piDecls ++ lets1, ald1)

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

-- | Level of a sort; 'lzero' for the sorts Canonical does not know.
sortLevel :: Sort -> TCM Term
sortLevel (Type l) = reallyUnLevelView l
sortLevel (SSet l) = reallyUnLevelView l
sortLevel _        = return (Level (Max 0 []))

-- | Translates the components of a Π-type @(x : A) → B@.
piParts :: Dom Type -> Abs Type -> [String] -> [CDecl] -> Seen -> Map String Sig
        -> TCM (PiP, [CDecl], Seen)
piParts a b names lets ald art = do
  (nm, names') <- case b of
    NoAbs _ _ -> (\ n -> (n, names))        <$> freshString "a"
    Abs n _   -> (\ n' -> (n', n' : names)) <$> freshString n
  lu <- sortLevel (getSort (unDom a))
  lv <- sortLevel (getSort (unAbs b))
  (eu, l1, a1) <- toCExpr lu names  [] lets ald False False art
  (ev, l2, a2) <- toCExpr lv names' [] l1   a1  False False art
  (ea, l3, a3) <- toCExpr (unEl $ unDom a) names [] l2 a2 False False art
  let art' = Map.insert nm (termSig (unEl $ unDom a)) art
  (eb, l4, a4) <- toCExpr (unEl $ unAbs b) names' [CDecl nm Nothing []] l3 a3 False False art'
  (l5, a5) <- withPi l4 a4
  return (PiP eu ev ea eb, l5, a5)

---------------------------------------------------------------------------
-- * Applications
---------------------------------------------------------------------------

-- | The terms of the applications in a list of eliminations.
appliedTerms :: [Elim' Term] -> [Term]
appliedTerms es = [ unArg t | Apply t <- es ]

-- | The successive function types before each argument, instantiated.
fnTypes :: Type -> [Term] -> [Type]
fnTypes t (a : as)
  | Pi _ b <- unEl t = t : fnTypes (absApp b a) as
fnTypes _ _ = []

-- | @stripPi ps ns t@ removes @length ps@ Π-binders from @t@, binding their
--   variables to the names @ps@ (pushed onto the bound names @ns@).
stripPi :: [String] -> [String] -> Term -> Maybe ([String], Term)
stripPi [] ns t = Just (ns, t)
stripPi (p : ps) ns (Pi _ b) = case b of
  Abs _ _   -> stripPi ps (p : ns) (unEl (unAbs b))
  NoAbs _ _ -> stripPi ps ns (unEl (unAbs b))
stripPi _ _ _ = Nothing

-- | Adapts an argument to the expected arity @k@.
--
--   With fewer binders, it is η-expanded.  With more binders, the extra ones
--   are wrapped in @Pi.mk@: the parameter has a Π-type as a term.
fixArg :: [String] -> Int -> Maybe Term -> CExpr -> [CDecl] -> Seen -> Map String Sig
       -> TCM (CExpr, [CDecl], Seen)
fixArg names k mty ce@(CExpr ps ls sp) lets ald art
  | m == k = return (ce, lets, ald)
  | m < k  = do
      ce' <- etaExtend (k - m) ce
      return (ce', lets, ald)
  | otherwise =
      case mty >>= stripPi (map name outer) names of
        Just (names', Pi dom b) -> do
          (pp, lets1, ald1) <- piParts dom b names' lets ald art
          (inner', lets2, ald2) <- fixArg names' 1 (Just (Pi dom b)) (CExpr inner [] sp) lets1 ald1 art
          return (CExpr outer ls (CSpine "Pi.mk" (piArgs pp ++ [inner'])), lets2, ald2)
        _ -> return (ce, lets, ald)
  where
    m = length ps
    (outer, inner) = splitAt k ps

-- | Applies a head symbol to its translated arguments, in η-long form.
--
--   Each argument is adapted to the arity expected by the signature
--   ('fixArg').  Missing arguments become fresh binders, returned so that
--   the caller adds them to the enclosing λ.  Arguments beyond the
--   signature (the head returns a Π-type as a term) are applied with @Pi.f@.
applyHead
  :: String          -- ^ Head symbol.
  -> Maybe Sym       -- ^ Its signatures, if known.
  -> [Term]          -- ^ The Agda arguments.
  -> [CExpr]         -- ^ The same arguments, translated.
  -> [String]        -- ^ Bound names.
  -> [CDecl]         -- ^ Context.
  -> Seen
  -> Map String Sig  -- ^ Signatures of the local variables.
  -> TCM (CSpine, [CDecl], [CDecl], Seen)
       -- ^ The spine, the binders added by η-expansion, the context and 'Seen'.
applyHead hd Nothing _ cargs _ lets ald _ =
  return (CSpine hd cargs, [], lets, ald)
applyHead hd (Just Sym { symSig = sg, symTy = mty }) terms cargs names lets0 ald0 art = do
  let ar   = length sg
      n    = length cargs
      ftys = maybe [] (`fnTypes` terms) mty
      expTy i = case drop i ftys of
        (t : _) | Pi dom _ <- unEl t -> Just (unEl (unDom dom))
        _                            -> Nothing
      fixStep (acc, ls, al) (i, k, ce) = do
        (ce', ls', al') <- fixArg names k (expTy i) ce ls al art
        return (acc ++ [ce'], ls', al')
      exStep (g, ls, al) (i, ce) =
        case drop i ftys of
          (t : _) | Pi dom b <- unEl t -> do
            let dty = unEl (unDom dom)
            (pp, ls1, al1)  <- piParts dom b names ls al art
            (ce', ls2, al2) <- fixArg names (arityOf dty) (Just dty) ce ls1 al1 art
            return (CSpine "Pi.f" (piArgs pp ++ [CExpr [] [] g, ce']), ls2, al2)
          _ -> return (appendArg g ce, ls, al)
  (fixed, lets1, ald1) <- foldM fixStep ([], lets0, ald0) (zip3 [0 ..] (map pArity sg) cargs)
  xs   <- replicateM (max 0 (ar - n)) (freshString "x")
  etas <- zipWithM etaVar xs (map pArity (drop n sg))
  (sp, lets2, ald2) <- foldM exStep (CSpine hd (fixed ++ etas), lets1, ald1)
                                    (zip [ar ..] (drop ar cargs))
  return (sp, map (\ x -> CDecl x Nothing []) xs, lets2, ald2)
  where
    appendArg (CSpine h as) ce = CSpine h (as ++ [ce])

---------------------------------------------------------------------------
-- * Terms
---------------------------------------------------------------------------

-- | Translates a type into a declaration, and records its signature.
toCDecl
  :: Term            -- ^ The type of the declaration.
  -> String          -- ^ Its name.
  -> [CEquation]     -- ^ Its equations.
  -> [String]        -- ^ Bound names.
  -> [CDecl]         -- ^ Context.
  -> Seen
  -> Bool            -- ^ Is it the goal (the context is then attached to it)?
  -> Map String Sig  -- ^ Signatures of the local variables.
  -> TCM (CDecl, [CDecl], Seen, Map String Sig)
toCDecl t n eqs bindnames lets ald tplvl art = do
  (ty, lets', ald') <- toCExpr t bindnames [] lets ald tplvl True art
  return (CDecl { name = n, typ = Just ty, equations = eqs }, lets', ald', insert n (termSig t) art)

-- | Translates a term.
--
--   In a type position, Π-binders become parameters; elsewhere, a Π-type is
--   encoded with @Pi@.  λ-binders always become parameters.
toCExpr
  :: Term            -- ^ The term.
  -> [String]        -- ^ Bound names.
  -> [CDecl]         -- ^ Parameters already met, the most recent first.
  -> [CDecl]         -- ^ Context.
  -> Seen
  -> Bool            -- ^ Is it the goal (the context is then attached to it)?
  -> Bool            -- ^ Is it in a type position?
  -> Map String Sig  -- ^ Signatures of the local variables.
  -> TCM (CExpr, [CDecl], Seen)
toCExpr t bindnames pidecl letdecl ald tplvl totyp art =
  case t of
    Pi a b | totyp -> do
      (newnames, na) <- case b of
        NoAbs _ _ -> do n' <- freshString "a"; return (bindnames, n')
        Abs n _   -> do n' <- freshString n;   return (n' : bindnames, n')
      (domdecl, lets, ald', art') <- toCDecl (unEl $ unDom a) na [] bindnames letdecl ald False art
      toCExpr (unEl $ unAbs b) newnames (domdecl : pidecl) lets ald' tplvl totyp art'
    Pi a b -> do
      (pp, lets, ald') <- piParts a b bindnames letdecl ald art
      return ( CExpr (reverse pidecl) (if tplvl then reverse lets else []) (CSpine "Pi" (piArgs pp))
             , lets, ald' )
    Lam _ b -> do
      let (newnames, n) = case b of
            NoAbs _ _ -> (bindnames, "_")
            Abs x _   -> (x : bindnames, x)
      toCExpr (unAbs b) newnames (CDecl n Nothing [] : pidecl) letdecl ald tplvl False art
    _ -> do
      (sp, extra, lets, ald') <- toCSpine t bindnames letdecl ald art
      return ( CExpr { params = reverse pidecl ++ extra
                     , lets   = if tplvl then reverse lets else []
                     , spine  = sp }
             , lets, ald' )

-- | Translates a neutral term or a sort.
--
--   Returns the binders added by η-expansion (see 'applyHead').
--   Unsupported terms are kept as their printed form.
toCSpine :: Term -> [String] -> [CDecl] -> Seen -> Map String Sig
         -> TCM (CSpine, [CDecl], [CDecl], Seen)
toCSpine t bindnames lets ald art =
  case t of
    Var i el -> do
      (as, lets', ald') <- elimsToCExpr el bindnames lets ald art
      let h = bindnames !! i
      applyHead h (localSym <$> Map.lookup h art) (appliedTerms el) as bindnames lets' ald' art
    Sort (Type l) -> do
      t' <- reallyUnLevelView l
      (a, lets', ald') <- toCExpr t' bindnames [] lets ald False False art
      return (CSpine { head = "Type", args = [a] }, [], lets', ald')
    Sort (SSet l) -> do
      t' <- reallyUnLevelView l
      (a, lets', ald') <- toCExpr t' bindnames [] lets ald False False art
      return (CSpine { head = "ß", args = [a] }, [], lets', ald')
    Sort IntervalUniv ->
      return (CSpine { head = "IUniv", args = [] }, [], lets, ald)
    Level l -> do
      t' <- reallyUnLevelView l
      toCSpine t' bindnames lets ald art
    Def qname e -> do
      (as, lets1, ald1) <- elimsToCExpr e bindnames lets ald art
      (lets2, ald2) <- gatherDatatypeInformations qname bindnames lets1 ald1
      sym <- globalSym qname
      applyHead (nameToString qname) (Just sym) (appliedTerms e) as bindnames lets2 ald2 art
    Con hd _ e -> do
      infos <- getConstInfo (conName hd)
      let dataname = case theDef infos of
            ConstructorDefn cd -> _conData cd
            _                  -> __IMPOSSIBLE__
      (as, lets1, ald1) <- elimsToCExpr e bindnames lets ald art
      (lets2, ald2) <- gatherDatatypeInformations dataname bindnames lets1 ald1
      sym <- globalSym (conName hd)
      applyHead (nameToString (conName hd)) (Just sym) (appliedTerms e) as bindnames lets2 ald2 art
    _ -> return (CSpine { head = P.prettyShow t, args = [] }, [], lets, ald)

-- | Translates the arguments of a list of eliminations.
--
--   Projections and interval applications are not supported; they are kept
--   as their printed form.
elimsToCExpr :: [Elim' Term] -> [String] -> [CDecl] -> Seen -> Map String Sig
             -> TCM ([CExpr], [CDecl], Seen)
elimsToCExpr es names lets ald art =
  case es of
    [] -> return ([], lets, ald)
    el : els -> do
      (e',   lets1, ald1) <- elimToCExpr el lets ald
      (els', lets2, ald2) <- elimsToCExpr els names lets1 ald1 art
      return (e' : els', lets2, ald2)
  where
    elimToCExpr :: Elim' Term -> [CDecl] -> Seen -> TCM (CExpr, [CDecl], Seen)
    elimToCExpr c ls al =
      case c of
        Apply t -> toCExpr (unArg t) names [] ls al False False art
        _       -> return (simpleExpr (P.prettyShow c), ls, al)

---------------------------------------------------------------------------
-- * Definitions
---------------------------------------------------------------------------

-- | Declares a definition (and what it depends on) to Canonical, if not
--   done yet.
--
--   * A datatype comes with its constructors and its recursor.
--   * A function comes with its clauses, as rewrite rules.
--   * @_⊔_@ comes with 'levelMaxEqs'.
gatherDatatypeInformations
  :: QName     -- ^ The definition.
  -> [String]  -- ^ Bound names.
  -> [CDecl]   -- ^ Context.
  -> Seen
  -> TCM ([CDecl], Seen)
gatherDatatypeInformations qn bindnames lets ald =
  if nameToString qn `member` ald then return (lets, ald)
  else do
    def <- getConstInfo qn
    sym <- globalSym qn
    let alrd = insert (nameToString qn) (symDecl sym) ald
        eqs  = if nameToString qn == "_⊔_" then levelMaxEqs else []
    (ty', lets1, ald1, _) <- toCDecl (unEl (defType def)) (nameToString qn) eqs bindnames lets alrd False mempty
    let letss = ty' : lets1
    case theDef def of
      DatatypeDefn dd@DatatypeData { _dataCons = cons } -> do
        defs <- mapM getConstInfo cons
        syms <- mapM globalSym cons
        let names = map nameToString cons
            tys   = zip (map (unEl . defType) defs) names
            alrd2 = foldl (\ m (k, s) -> insert k (symDecl s) m) ald1 (zip names syms)
        (ctys, lets2, ald2) <- foldlM (\ (acc, ls, al) (t, n) -> do
                                  (nt, ls', al', _) <- toCDecl t n [] bindnames ls al False mempty
                                  return (nt : acc, ls', al'))
                                ([], letss, alrd2) tys
        let ctorDs = reverse ctys
        lq <- fromMaybe __IMPOSSIBLE__ <$> getName' BuiltinLevel
        (lets3, ald3) <- gatherDatatypeInformations lq [] lets2 ald2
        mrec <- mkRecursor (_dataPars dd) ty' ctorDs
        case mrec of
          Nothing        -> return (ctorDs ++ lets3, ald3)
          Just (recD, s) -> return (recD : ctorDs ++ lets3, insert (name recD) s ald3)
      FunctionDefn FunctionData { _funClauses = cls } -> do
        (eqs', lets2, ald2) <- clausesToEquations qn (symDecl sym) cls lets1 ald1
        return (ty' { equations = eqs' } : lets2, ald2)
      _ -> return (letss, ald1)

-- ** Clauses

-- | Translates the clauses of a function, skipping the unsupported ones.
clausesToEquations :: QName -> Sig -> [Clause] -> [CDecl] -> Seen
                   -> TCM ([CEquation], [CDecl], Seen)
clausesToEquations qn sg cls lets ald =
  foldlM (\ (eqs, ls, al) cl -> do
            (me, ls', al') <- clauseToEquation qn sg cl ls al
            return (eqs ++ maybe [] pure me, ls', al'))
         ([], lets, ald) cls

-- | Translates a clause into a rewrite rule, in η-long form.
--
--   The clause is skipped ('Nothing') if it has no body, an unsupported
--   pattern, or more patterns than the signature, or if its body contains an
--   unsolved meta or uses a function that the user cannot write (see 'isHidden').
clauseToEquation :: QName -> Sig -> Clause -> [CDecl] -> Seen
                 -> TCM (Maybe CEquation, [CDecl], Seen)
clauseToEquation qn sg cl lets ald =
  case clauseBody cl of
    Nothing   -> skip
    Just body0 -> do
      -- A body that is still a hole, or contains one, is not a definition yet.
      body   <- instantiateFull body0
      hidden <- or <$> mapM isHidden (namesIn body :: [QName])
      if hidden || not (noMetas body) then skip else do
        let tel  = clauseTel cl
            pats = map namedArg (namedClausePats cl)
            ar   = length sg
            n    = length pats
        ns <- mapM freshString (teleNames tel)
        let bindn = reverse ns                       -- Var i is bindn !! i
            art0  = Map.fromList
                      [ (x, termSig (unEl (snd (unDom d)))) | (x, d) <- zip ns (telToList tel) ]
        mps <- mapM (patToCExpr bindn) pats
        case sequence mps of
          Just lhs0 | n <= ar -> do
            l                 <- zipWithM etaTo (map pArity sg) lhs0
            (xs, bindn', b')  <- peel (ar - n) bindn body
            (e, lets', ald')  <- toCExpr b' bindn' [] lets ald False False art0
            let k = ar - n - length xs
                j = length (params e)
            if j > k then skip else do
              e' <- etaExtend (k - j) e
              let extra = map simpleExpr (xs ++ map name (params e'))
              return ( Just (CEquation (CSpine (nameToString qn) (l ++ extra)) (spine e') True)
                     , lets', ald' )
          _ -> skip
  where skip = return (Nothing, lets, ald)

-- | A pattern-matching lambda or the auxiliary function of a @with@: their
--   names cannot be written in Agda, so a solution must not unfold to them.
isHidden :: QName -> TCM Bool
isHidden q = do
  d <- theDef <$> getConstInfo q
  return $ case d of
    Function { funExtLam = Just _ } -> True
    Function { funWith = Just _ }   -> True
    _                               -> False

-- | Translates a pattern into an argument of a left-hand side.
--
--   A dot pattern becomes a fresh wildcard; the parameters of a constructor,
--   absent from Agda patterns, become fresh wildcards.  Literals,
--   projections and cubical patterns are not supported ('Nothing').
patToCExpr :: [String] -> DeBruijnPattern -> TCM (Maybe CExpr)
patToCExpr names p = case p of
  VarP _ x -> return . Just $ simpleExpr (names !! dbPatVarIndex x)
  DotP _ _ -> Just . simpleExpr <$> freshString "w"
  ConP c _ ps -> do
    np   <- conParCount (conName c)
    ws   <- replicateM np (simpleExpr <$> freshString "p")
    subs <- mapM (patToCExpr names . namedArg) ps
    return $ (\ ss -> CExpr [] [] (CSpine (nameToString (conName c)) (ws ++ ss)))
               <$> sequence subs
  _ -> return Nothing

-- | Number of parameters of the datatype of a constructor.
conParCount :: QName -> TCM Int
conParCount q = do
  d <- getConstInfo q
  return $ case theDef d of
    ConstructorDefn cd -> _conPars cd
    _                  -> __IMPOSSIBLE__

-- | @peel k ns t@ removes up to @k@ λ-binders of @t@ with fresh names.
--   Returns these names, the extended bound names, and the body.
peel :: Int -> [String] -> Term -> TCM ([String], [String], Term)
peel k ns (Lam _ b) | k > 0 = do
  let nm = case b of { Abs n _ -> n; NoAbs n _ -> n }
  x <- freshString nm
  let ns' = case b of { Abs{} -> x : ns; NoAbs{} -> ns }
  (xs, ns'', t) <- peel (k - 1) ns' (unAbs b)
  return (x : xs, ns'', t)
peel _ ns t = return ([], ns, t)
