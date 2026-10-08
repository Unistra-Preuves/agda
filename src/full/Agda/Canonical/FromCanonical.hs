-- | Printing of Canonical's answers in Agda syntax.
--
--   * Implicit arguments of applications are omitted: Agda infers them.
--
--   * Implicit binders (of λs and patterns) are kept, in braces, only when
--     they are used in the printed term.
--
--   * @Path.mk@ and @Path.f@ (see "Agda.Canonical.Cubical") are printed as
--     λs and applications too, and symbols are printed under the name they
--     have in scope when it differs ('giAliases').
--
--   * @Pi@, @Pi.mk@ and @Pi.f@ (see "Agda.Canonical.Builtin") are printed
--     back as Π-types, λs and applications.
--
--   * A record projection @f pars r@ is printed as a postfix projection
--     @r .f@, and the constructor of a record without named constructor as
--     a record expression @record { f₁ = a₁ ; … }@.
--
--   * Recursors @D.rec@ (see "Agda.Canonical.Recursor") become
--     pattern-matching lambdas.  Agda cannot infer the type of such a
--     lambda applied to an argument, so the motive found by Canonical is
--     given in a @let@:
--
--     > let r : (k : I) → D ps k → C k ; r = λ { _ (c xs) → … } in r i major
--
--     Since these lambdas are not recursive, an induction hypothesis is
--     printed as a recursive call to the function containing the hole.
--
--   * The suffixes added by 'Agda.Canonical.Utils.freshString' are removed,
--     and primes are added to avoid shadowing a name in scope.
--
--   When the answer is a recursor applied to a variable of the context,
--   'canonicalSplit' describes it as a case split instead, so that it can be
--   written as clauses with real recursive calls.

module Agda.Canonical.FromCanonical
  ( cexprToAgda, cexprToAgdaAs
  , unwrapAnswer
  , usesNestedIH
  , outOfScopeUses
  , lambdaClause
    -- * Case splits
  , Split(..), SplitTarget(..), SplitBranch(..), ClauseNames(..)
  , canonicalSplit
  ) where

import Control.Monad (guard)
import Data.List (elemIndex, intercalate, isSuffixOf, nub)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set qualified as Set

import Agda.Canonical.Types
import Agda.Syntax.Common (Hiding (..), MetaId)

---------------------------------------------------------------------------
-- * Documents
---------------------------------------------------------------------------

-- | Printed text with its precedence.
data Doc = Doc
  { docPrec :: Int
      -- ^ 0 for λ and Π, 1 for a mixfix operator, 2 for an application,
      --   3 for an atom.
  , docText :: String
      -- ^ The text, without enclosing parentheses.
  }

-- | A name, or any text that never needs parentheses.
atom :: String -> Doc
atom = Doc 3

-- | The text of a document in a position requiring at least precedence @n@.
atP :: Int -> Doc -> String
atP n (Doc p s)
  | p >= n    = s
  | otherwise = "(" ++ s ++ ")"

-- | Application.
app :: Doc -> [Doc] -> Doc
app d [] = d
app d ds = Doc 2 (unwords (map (atP 3) (d : ds)))

-- | λ-abstraction over already printed binders.
lam :: [String] -> Doc -> Doc
lam [] d = d
lam bs d = Doc 0 ("λ " ++ unwords bs ++ " → " ++ docText d)

-- | Application of a name, in mixfix notation when it has enough arguments.
named :: String -> [Doc] -> Doc
named h ds
  -- A qualified operator (@M._+_@) is applied in prefix form.
  | '.' `elem` h = app (atom h) ds
  | holes > 0, length ds >= holes =
      let (now, later) = splitAt holes ds
          txt = unwords (filter (not . null) (interleave parts (map (atP 2) now)))
      in app (Doc 1 txt) later
  | otherwise = app (atom h) ds
  where
    parts = splitOnHoles h
    holes = length parts - 1
    interleave (p : ps) (a : as) = p : a : interleave ps as
    interleave ps [] = ps
    interleave [] _  = []
    splitOnHoles s = case break (== '_') s of
      (p, _ : rest) -> p : splitOnHoles rest
      (p, [])       -> [p]

-- | A binder or a pattern with the given visibility.
wrap :: Hiding -> String -> String
wrap NotHidden  s = s
wrap Hidden     s = "{" ++ s ++ "}"
wrap Instance{} s = "⦃ " ++ s ++ " ⦄"

---------------------------------------------------------------------------
-- * Recursors
---------------------------------------------------------------------------

-- | A computation rule of a recursor, i.e. a constructor.
data Branch = Branch
  { brCtor   :: String
      -- ^ Name of the constructor.
  , brFields :: Int
      -- ^ Number of fields.
  , brIhs    :: [Int]
      -- ^ For each induction hypothesis, the index of its field.
  }

-- | The layout of a recursor (see "Agda.Canonical.Recursor").
data RecInfo = RecInfo
  { riPars     :: Int
      -- ^ Number of parameters of the datatype.
  , riIdx      :: Int
      -- ^ Number of indices of the datatype.
  , riBranches :: [Branch]
      -- ^ One branch per constructor, in order.
  , riParams   :: [CDecl]
      -- ^ The parameters of the type of the recursor: level, parameters of
      --   the datatype, motive, minor premises, indices, major premise.
  }

-- | The recursors declared in the context sent to Canonical, recovered from
--   their types and computation rules.
recInfos :: [CDecl] -> Map String RecInfo
recInfos ds = Map.fromList
  [ (name d, ri) | d <- ds, ".rec" `isSuffixOf` name d, Just ri <- [recInfo d] ]

-- | The layout of a recursor: the parameters precede the motive.
recInfo :: CDecl -> Maybe RecInfo
recInfo (CDecl _ (Just (CExpr ps _ _)) eqs) = do
  mi  <- elemIndex "motive" (map (stripFresh . name) ps)
  let np = mi - 1
      ni = length ps - np - length eqs - 3
  brs <- mapM (branch np) eqs
  if np < 0 || ni < 0 then Nothing else Just (RecInfo np ni brs ps)
  where
    branch np (CEquation (CSpine _ las) (CSpine _ ras) _) = case reverse las of
      CExpr _ _ (CSpine c cas) : _ -> do
        let flds = [ f | CExpr _ _ (CSpine f _) <- drop np cas ]
            ihField (CExpr _ _ (CSpine _ ias)) = case reverse ias of
              CExpr _ _ (CSpine f _) : _ -> elemIndex f flds
              []                         -> Nothing
        ihs <- mapM ihField (drop (length flds) ras)
        Just (Branch c (length flds) ihs)
      [] -> Nothing
recInfo _ = Nothing

-- | Number of parameters, of constructors, and total arity of a recursor.
recShape :: RecInfo -> (Int, Int, Int)
recShape ri = (np, k, np + k + riIdx ri + 3)
  where np = riPars ri
        k  = length (riBranches ri)

---------------------------------------------------------------------------
-- * Environment
---------------------------------------------------------------------------

-- | What a variable bound in the answer stands for.
data Bound
  = Local String
      -- ^ A variable, with its Agda name.
  | IH String
      -- ^ An induction hypothesis on the given field (Canonical name),
      --   printed as a recursive call on that field alone.
  | Call [String] [Maybe String] String
      -- ^ An induction hypothesis on the given field, printed as a recursive
      --   call with the given named implicit arguments (@{x = y}@), then the
      --   given explicit arguments, the field taking the place of 'Nothing'.
  | Hyp Doc
      -- ^ An induction hypothesis of the context, printed as the recursive
      --   call it stands for (see "Agda.Canonical.Induction").

-- | Printing environment.
data Env = Env
  { eInfo  :: GoalInfo
      -- ^ Signatures of the symbols.
  , eRecs  :: Map String RecInfo
      -- ^ Known recursors.
  , eSelf  :: String
      -- ^ Name used for recursive calls.
  , eBound :: Map String Bound
      -- ^ Variables bound in the answer, by Canonical name.
  , eUsed  :: Set String
      -- ^ Agda names already in scope.
  , eFresh :: Int
      -- ^ Counter for the names introduced by η-expansion.
  , eExplicit :: Bool
      -- ^ Print implicit arguments, in braces.
  }

-- | The initial environment.
initEnv
  :: Bool      -- ^ Print implicit arguments?
  -> GoalInfo  -- ^ Information about the goal.
  -> [CDecl]   -- ^ The context sent to Canonical, to recover the recursors.
  -> String    -- ^ Name of the function containing the hole, for recursive calls.
  -> Env
initEnv explicit info ctx self = Env
  { eInfo     = info
  , eRecs     = recInfos ctx
  , eSelf     = self
  , eBound    = Map.map (\ (op, s) -> Hyp (Doc (if op then 1 else 2) s)) (giHyps info)
  , eUsed     = Set.fromList (giNames info ++ Map.keys (giGlobals info))
  , eFresh    = 0
  , eExplicit = explicit
  }

-- | Readable name: the suffix added by 'Agda.Canonical.Utils.freshString' is removed.
stripFresh :: String -> String
stripFresh s = case takeWhile (/= '.') s of
  ""  -> "x"
  "_" -> "x"
  b   -> b

-- | Binds a variable to an Agda name not yet in scope (adding primes if needed).
bind :: String -> Env -> (String, Env)
bind x env = (x', env { eBound = Map.insert x (Local x') (eBound env)
                      , eUsed  = Set.insert x' (eUsed env) })
  where
    x' = case filter (`Set.notMember` eUsed env) (iterate (++ "'") (stripFresh x)) of
      n : _ -> n
      []    -> stripFresh x

-- | A fresh Canonical name.
freshVar :: Env -> (String, Env)
freshVar env = ("x.η" ++ show (eFresh env), env { eFresh = eFresh env + 1 })

-- | Prints binders.  Explicit binders are always kept (as @_@ when unused);
--   implicit ones only when they are used, or when a later implicit binder
--   (before the next explicit one) is used, so that positions are preserved.
binders :: Env -> (String -> Bool) -> [(String, Hiding)] -> ([String], Env)
binders env0 used = go env0
  where
    go e [] = ([], e)
    go e ((x, h) : rest)
      | used x =
          let (x', e1) = bind x e
              (r, e2)  = go e1 rest
          in (wrap h x' : r, e2)
      | h == NotHidden || any (used . fst) (takeWhile ((/= NotHidden) . snd) rest) =
          let (r, e1) = go e rest in (wrap h "_" : r, e1)
      | otherwise = go e rest

-- | The arguments actually printed for the head @h@ (see 'spineDoc').
visibleArgs :: Env -> String -> [CExpr] -> [CExpr]
visibleArgs env h as = case Map.lookup h (eBound env) of
  Just (Local _)  -> as
  Just (IH f)     -> [CExpr [] [] (CSpine f as)]
  Just (Call _ _ f) -> [CExpr [] [] (CSpine f as)]
  Just (Hyp _) | eExplicit env -> as
  Just (Hyp _)    -> [ a | (a, NotHidden) <- zip as (sigHidings env h ++ repeat NotHidden) ]
  Nothing -> case (h, as) of
    ("Type", [_])          -> as
    ("ß", [_])             -> as
    ("Pi", [_, _, a, b])   -> [a, b]
    ("Pi.mk", _ : _ : _ : _ : rest) -> rest
    ("Pi.f",  _ : _ : _ : _ : rest) -> rest
    ("Path.mk", _ : _ : _ : _ : rest) -> rest
    ("Path.f",  _ : _ : _ : _ : rest) -> rest
    _ | Just ri <- Map.lookup h (eRecs env)
      , let (np, k, total) = recShape ri
      , length as >= total
      -> as   -- all of them occur in the typed elimination
    _ | Just (np, _) <- Map.lookup h (giRecCons (eInfo env))
      -> drop np as   -- all the fields are named in the record expression
    _ | eExplicit env -> as
    _ -> [ a | (a, NotHidden) <- zip as (sigHidings env h ++ repeat NotHidden) ]

-- | Visibilities of the parameters of a symbol; empty if unknown.
sigHidings :: Env -> String -> [Hiding]
sigHidings env h = maybe [] (map pHiding) (lookupSig (eInfo env) h)

-- | Whether @x@ occurs in the printed term (omitted implicit arguments do not count).
occurs :: Env -> String -> CExpr -> Bool
occurs env x (CExpr _ _ sp) = occursS env x sp

-- | 'occurs' for a spine.
occursS :: Env -> String -> CSpine -> Bool
occursS env x (CSpine h as) = h == x || any (occurs env x) (visibleArgs env h as)

-- | η-expands an expression until it has at least @n@ binders.
etaTo :: Int -> CExpr -> Env -> (CExpr, Env)
etaTo n ce@(CExpr ps ls (CSpine h as)) env
  | length ps >= n = (ce, env)
  | otherwise      = (CExpr (ps ++ map (\x -> CDecl x Nothing []) xs) ls
                            (CSpine h (as ++ map simpleExpr xs)), env')
  where
    (xs, env') = foldr (\_ (acc, e) -> let (x, e1) = freshVar e in (x : acc, e1))
                       ([], env) [1 .. n - length ps]

---------------------------------------------------------------------------
-- * Printing
---------------------------------------------------------------------------

-- | Prints an answer of Canonical in Agda syntax.
cexprToAgda
  :: Bool      -- ^ Print implicit arguments, in braces?
  -> GoalInfo  -- ^ Information about the goal.
  -> [CDecl]   -- ^ The context sent to Canonical, to recover the recursors.
  -> String    -- ^ Name of the function containing the hole, for recursive calls.
  -> CExpr     -- ^ The answer.
  -> String
cexprToAgda explicit info = cexprToAgdaAs explicit info "Goal"

-- | 'cexprToAgda' for a term whose binders are those of the type of a symbol.
cexprToAgdaAs :: Bool -> GoalInfo -> String -> [CDecl] -> String -> CExpr -> String
cexprToAgdaAs explicit info x ctx self e = docText (expr env hid e)
  where
    env = initEnv explicit info ctx self
    hid = maybe [] (map pHiding) (lookupSig info x)

-- | The solution of the goal in an answer of Canonical, and the values of
--   the metas of the goal.  If the goal is stated through a continuation,
--   the answer is @λ k → k t₁ … tₙ [B] b@, where the binders @Δ@ are
--   declared in the context: the solution is @λ Δ → b@ and
--   the value of the meta @?mᵢ@ is @tᵢ@; the last binders of @Δ@ coming from
--   a path of functions are put back after the first binder of @b@.
--
--   Then the first binders of the solution, which stand for the variables
--   of the context refolded into the goal ('giRefold'), are unfolded: they
--   are replaced by these variables.  'Nothing' if the answer does not have
--   this shape.
unwrapAnswer :: GoalInfo -> CExpr -> Maybe (CExpr, [(MetaId, CExpr)])
unwrapAnswer info e = do
  (s, vals) <- case giCont info of
    Nothing -> Just (e, [])
    Just c  -> case e of
      CExpr [_] _ (CSpine _ as)
        | length as == length (contMetas c) + (if contTyped c then 2 else 1)
        , CExpr bps _ bsp <- last as ->
            let outer            = [ CDecl x Nothing [] | x <- contOuter c ]
                (delta, swapped) = splitAt (length outer - contSwap c) outer
                (first, rest)    = splitAt 1 bps
            in Just (CExpr (delta ++ first ++ swapped ++ rest) [] bsp, zip (contMetas c) as)
      _ -> Nothing
  s' <- unfold s
  return (s', vals)
  where
    xs = giRefold info
    unfold (CExpr ps _ sp)
      | length ps < length xs = Nothing
      | otherwise =
          let (qs, rest) = splitAt (length xs) ps
              sub        = Map.fromList (zip (map name qs) (map simpleExpr xs))
          in Just (substE sub (CExpr rest [] sp))

-- | Does the answer use the induction hypothesis of a recursor that is
--   printed as a pattern-matching lambda?  Such a lambda is not recursive,
--   so the hypothesis cannot be printed: it is not a call of the function
--   containing the hole.  The recursor split on by 'canonicalSplit' does
--   not count.
usesNestedIH :: GoalInfo -> [CDecl] -> String -> CExpr -> Bool
usesNestedIH info ctx self e = case canonicalSplit info ctx self e of
  Just _  -> False   -- its branches are checked by 'canonicalSplit'
  Nothing -> nestedIH (initEnv False info ctx self) e

-- | 'usesNestedIH' for any recursor.
nestedIH :: Env -> CExpr -> Bool
nestedIH env (CExpr _ _ (CSpine h as)) = here || any (nestedIH env) as
  where
    here = case Map.lookup h (eRecs env) of
      Just ri | let (np, k, total) = recShape ri, length as >= total ->
        or [ any (\ (ih, _) -> occurs env2 ih body) pairs
           | (br, m) <- zip (riBranches ri) (take k (drop (np + 2) as))
           , let (_, pairs, body, env2) = branchParts env br m ]
      _ -> False

-- | The variables of the context that the user cannot refer to
--   ('giOutOfScope') and that occur in the printed answer, where they are
--   printed @_@.
outOfScopeUses
  :: Bool      -- ^ Are implicit arguments printed?
  -> GoalInfo  -- ^ Information about the goal.
  -> [CDecl]   -- ^ The context sent to Canonical, to recover the recursors.
  -> String    -- ^ Name of the function containing the hole, for recursive calls.
  -> CExpr     -- ^ The answer.
  -> [String]
outOfScopeUses explicit info ctx self = outOfScopeIn (initEnv explicit info ctx self)

-- | 'outOfScopeUses' in a given environment.
outOfScopeIn :: Env -> CExpr -> [String]
outOfScopeIn env = nub . go Set.empty
  where
    go bound (CExpr ps _ (CSpine h as)) =
      [ h | h `elem` giOutOfScope (eInfo env), h `Set.notMember` bound', h `Map.notMember` eBound env ]
      ++ concatMap (go bound') (visibleArgs env h as)
      where bound' = foldr (Set.insert . name) bound ps

-- | The λ-binders of an answer, to be written as patterns of the clause,
--   and its body.  As with 'binders', explicit binders are always kept
--   ('Nothing' when unused, i.e. @_@), implicit ones only when they are used
--   or a later implicit one (before the next explicit one) is used.  The
--   names do not shadow the names in scope.  'Nothing' if the answer is not
--   a λ.
lambdaClause
  :: Bool      -- ^ Print implicit arguments, in braces?
  -> GoalInfo  -- ^ Information about the goal.
  -> [CDecl]   -- ^ The context sent to Canonical, to recover the recursors.
  -> String    -- ^ Name of the function containing the hole, for recursive calls.
  -> CExpr     -- ^ The answer.
  -> Maybe ([(Maybe String, Hiding)], String)
lambdaClause _ _ _ _ (CExpr [] _ _) = Nothing
lambdaClause explicit info ctx self (CExpr ps _ sp) =
  Just (go env0 (zip (map name ps) (hid ++ repeat NotHidden)))
  where
    env0 = initEnv explicit info ctx self
    hid  = maybe [] (map pHiding) (lookupSig info "Goal")
    used x = occursS env0 x sp
    go e [] = ([], docText (spineDoc e sp))
    go e ((x, h) : rest)
      | used x =
          let (x', e1) = bind x e
              (r, b)   = go e1 rest
          in ((Just x', h) : r, b)
      | h == NotHidden || any (used . fst) (takeWhile ((/= NotHidden) . snd) rest) =
          let (r, b) = go e rest in ((Nothing, h) : r, b)
      | otherwise = go e rest

-- | An expression whose binders have the given visibilities (explicit by default).
expr :: Env -> [Hiding] -> CExpr -> Doc
expr env hs (CExpr ps _ sp) = lam bs (spineDoc env' sp)
  where (bs, env') = binders env (\x -> occursS env x sp) (zip (map name ps) (hs ++ repeat NotHidden))

-- | An expression whose binders are explicit.
arg :: Env -> CExpr -> Doc
arg env = expr env []

-- | A spine, with special cases for the declarations of "Agda.Canonical.Builtin"
--   and for recursors.
spineDoc :: Env -> CSpine -> Doc
spineDoc env (CSpine h as) = case Map.lookup h (eBound env) of
  Just (Local x) -> app (atom x) (map (arg env) as)
  Just (IH f)    -> named (eSelf env) [spineDoc env (CSpine f as)]
  Just (Call imps cargs f)
    | null imps -> named (eSelf env) explicits
    | otherwise -> app (atom (eSelf env)) (map atom imps ++ explicits)   -- prefix form
    where explicits = [ maybe (spineDoc env (CSpine f as)) atom a | a <- cargs ]
  Just (Hyp d)
    | eExplicit env -> app d [ if hid == NotHidden then arg env a else atom (wrap hid (docText (arg env a)))
                             | (a, hid) <- zip as (sigHidings env h ++ repeat NotHidden) ]
    | otherwise     -> app d (map (arg env) (visibleArgs env h as))
  Nothing
    | h `elem` giOutOfScope (eInfo env) -> atom "_"   -- left to Agda
    | otherwise    -> special h as
  where
    special "Type" [l] = setDoc env "Set" l
    special "ß"    [l] = setDoc env "SSet" l
    special "Pi" [_, _, a, b] = piDoc env a b
    special "Pi.mk" (_ : _ : _ : _ : f : rest) = applyTo env f rest
    special "Pi.f"  (_ : _ : _ : _ : p : rest) = applyTo env p rest
    special "Path.mk" (_ : _ : _ : _ : f : rest) = applyTo env f rest
    special "Path.f"  (_ : _ : _ : _ : p : rest) = applyTo env p rest
    special _ _
      | Just ri <- Map.lookup h (eRecs env), Just d <- recDoc env ri as = d
    special _ _
      | Just np <- Map.lookup h (giProjs (eInfo env)), r : rest <- drop np as =
          Doc 2 (unwords (atP 2 (arg env r) : ('.' : shown) : map (atP 3 . arg env) rest))
    special _ _
      | Just (np, fs) <- Map.lookup h (giRecCons (eInfo env)), length as == np + length fs =
          atom ("record {" ++ concat [ " " ++ f ++ " = " ++ docText (arg env a) ++ sep
                                     | (f, a, sep) <- zip3 fs (drop np as) (map (const " ;") (drop 1 fs) ++ [" "]) ]
                ++ "}")
    special _ _
      | eExplicit env = explicitApp env shown (zip as (sigHidings env h ++ repeat NotHidden))
      | otherwise     = named shown (map (arg env) (visibleArgs env h as))
    shown | Map.member h (giGlobals (eInfo env)) || Map.member h (giAliases (eInfo env)) = globalName env h
          | otherwise = stripFresh h

-- | The name under which a global symbol is printed.
globalName :: Env -> String -> String
globalName env h = Map.findWithDefault h h (giAliases (eInfo env))

-- | Application with implicit arguments in braces.  Mixfix notation is only
--   used when all arguments are explicit.
explicitApp :: Env -> String -> [(CExpr, Hiding)] -> Doc
explicitApp env h has
  | all ((== NotHidden) . snd) has = named h ds
  | otherwise = app (atom h) [ if hid == NotHidden then d else atom (wrap hid (docText d))
                             | (d, hid) <- zip ds (map snd has) ]
  where ds = map (arg env . fst) has

-- | Application of an expression; arguments are appended to a spine directly.
applyTo :: Env -> CExpr -> [CExpr] -> Doc
applyTo env (CExpr [] _ (CSpine g gs)) rest = spineDoc env (CSpine g (gs ++ rest))
applyTo env f rest = app (arg env f) (map (arg env) rest)

-- | A universe: @Set@, @Set₁@, … for closed levels, @Set l@ otherwise.
setDoc :: Env -> String -> CExpr -> Doc
setDoc env s l = case levelNat l of
  Just 0  -> atom s
  Just n  -> atom (s ++ map subscript (show n))
  Nothing -> app (atom s) [arg env l]
  where
    subscript c = toEnum (fromEnum c - fromEnum '0' + fromEnum '₀')
    levelNat (CExpr [] _ (CSpine "lzero" [])) = Just (0 :: Int)
    levelNat (CExpr [] _ (CSpine "lsuc" [k])) = (+ 1) <$> levelNat k
    levelNat _ = Nothing

-- | @Pi u v A B@ is printed as @(x : A) → B x@, or @A → B@ if @x@ does not occur.
piDoc :: Env -> CExpr -> CExpr -> Doc
piDoc env a b = case b of
  CExpr (x : rest) _ sp
    | occurs env (name x) body ->
        let (x', env') = bind (name x) env
        in Doc 0 ("(" ++ x' ++ " : " ++ docText (arg env a) ++ ") → " ++ docText (arg env' body))
    | otherwise -> Doc 0 (atP 1 (arg env a) ++ " → " ++ docText (arg env body))
    where body = CExpr rest [] sp
  CExpr [] _ _ -> let (b', env') = etaTo 1 b env in piDoc env' a b'

-- | @D.rec l pars motive minors idx major extra@ is printed by 'typedElim',
--   or 'Nothing' if it is partially applied.
recDoc :: Env -> RecInfo -> [CExpr] -> Maybe Doc
recDoc env ri as = case drop (total - 1) as of
  major : extra -> Just (typedElim env ri as major extra)
  []            -> Nothing
  where
    (_, _, total) = recShape ri

-- | The pattern-matching lambda of a recursor, whose clauses first match
--   @ni@ indices with @_@.
patLam :: Env -> RecInfo -> Int -> [CExpr] -> Doc
patLam env ri ni as
  | k == 0    = Doc 0 ("λ " ++ concat (replicate ni "_ ") ++ "()")
  | otherwise = Doc 0 ("λ { " ++ intercalate " ; "
                         [ concat (replicate ni "_ ") ++ branchDoc env np br m
                         | (br, m) <- zip (riBranches ri) minors ] ++ " }")
  where
    (np, k, _) = recShape ri
    minors = take k (drop (np + 2) as)

-- | @let r : T ; r = λ { … } in r is major extra@, where @T@ is the motive
--   as a Π-type over the indices and the eliminated value.
typedElim :: Env -> RecInfo -> [CExpr] -> CExpr -> [CExpr] -> Doc
typedElim env ri as major extra =
  Doc 0 ("let " ++ r ++ " : " ++ docText ty ++ " ; " ++ r ++ " = "
         ++ docText (patLam env1 ri ni as) ++ " in " ++ docText call)
  where
    (np, k, _) = recShape ri
    ni         = riIdx ri
    (rv, env0) = freshVar env
    (r, env1)  = bind ("r" ++ dropWhile (/= '.') rv) env0
    -- The motive, with one binder per index and one for the value.
    (CExpr mps _ mb, env2) = etaTo (ni + 1) (as !! (np + 1)) env1
    ps     = riParams ri
    idxDs  = take ni (drop (np + 2 + k) ps)
    majDs  = drop (np + 2 + k + ni) ps
    -- Level and parameters are replaced by the actual arguments, indices
    -- by the binders of the motive.
    sub    = Map.fromList $
               zip (map name (take (np + 1) ps)) (take (np + 1) as) ++
               zip (map name idxDs) (map (simpleExpr . name) mps)
    tele   = [ (name m, substE sub (fromMaybe (simpleExpr "_") (typ d)))
             | (m, d) <- zip mps (idxDs ++ majDs) ]
    ty     = piTele env2 tele (CExpr [] [] mb)
    call   = app (atom r) (map (arg env) (take ni (drop (np + 2 + k) as) ++ major : extra))

-- | A Π-type @(x₁ : A₁) → … → B@; non-dependent binders are printed @A → B@.
piTele :: Env -> [(String, CExpr)] -> CExpr -> Doc
piTele env [] body = typeDoc env body
piTele env ((x, a) : rest) body
  | any (occurs env x . snd) rest || occurs env x body =
      let (x', env') = bind x env
      in Doc 0 ("(" ++ x' ++ " : " ++ docText (typeDoc env a) ++ ") → " ++ docText (piTele env' rest body))
  | otherwise = Doc 0 (atP 1 (typeDoc env a) ++ " → " ++ docText (piTele env rest body))

-- | An expression in a type position: its binders are Π-binders.
typeDoc :: Env -> CExpr -> Doc
typeDoc env (CExpr [] _ sp) = spineDoc env sp
typeDoc env (CExpr ps _ sp) =
  piTele env [ (name d, fromMaybe (simpleExpr "_") (typ d)) | d <- ps ] (CExpr [] [] sp)

-- | Substitution of expressions for variables, with one step of β-reduction
--   when a substituted λ is applied.
substE :: Map String CExpr -> CExpr -> CExpr
substE sub (CExpr ps ls sp) = CExpr (map substD ps) (map substD ls) (substS sub' sp)
  where
    sub'     = foldr (Map.delete . name) sub ps
    substD d = d { typ = substE sub' <$> typ d }

-- | 'substE' for a spine.
substS :: Map String CExpr -> CSpine -> CSpine
substS sub (CSpine h as) = case Map.lookup h sub of
  Nothing                          -> CSpine h as'
  Just (CExpr [] _ (CSpine h' bs)) -> CSpine h' (bs ++ as')
  Just (CExpr qs _ sp)             ->
    let CSpine h' bs = substS (Map.fromList (zip (map name qs) as')) sp
    in CSpine h' (bs ++ drop (length qs) as')
  where as' = map (substE sub) as

-- | Splits a minor premise into its fields, its induction hypotheses (with
--   their fields) and its body.  The induction hypotheses are bound as 'IH'.
branchParts :: Env -> Branch -> CExpr -> ([CDecl], [(String, String)], CExpr, Env)
branchParts env (Branch _ nf ihs) m = (fps, pairs, body, env2)
  where
    (CExpr mps _ msp, env1) = etaTo (nf + length ihs) m env
    (bps, more) = splitAt (nf + length ihs) mps
    (fps, ips)  = splitAt nf bps
    body  = CExpr more [] msp
    pairs = [ (name ih, name (fps !! i)) | (ih, i) <- zip ips ihs ]
    env2  = env1 { eBound = foldr (\ (ih, f) -> Map.insert ih (IH f)) (eBound env1) pairs }

-- | A clause @c fs → body@ of the pattern-matching lambda, from a minor premise.
branchDoc :: Env -> Int -> Branch -> CExpr -> String
branchDoc env np br@(Branch c _ _) m =
  atP 3 pat ++ " → " ++ docText (arg env3 body)
  where
    (fps, _, body, env2) = branchParts env br m
    used x = occurs env2 x body   -- a field counts as used through its IH
    hs    = drop np (sigHidings env c)
    (pstrs, env3) = binders env2 used (zip (map name fps) (hs ++ repeat NotHidden))
    pat | any ((`elem` ["{", "⦃"]) . take 1) pstrs = app (atom c') (map atom pstrs)
        | otherwise                                = named c' (map atom pstrs)
    c' = globalName env c

---------------------------------------------------------------------------
-- * Case splits
---------------------------------------------------------------------------

-- | A case split, read from an answer @D.rec … x@.
data Split = Split
  { spTarget   :: SplitTarget
      -- ^ What to split on.
  , spBranches :: [SplitBranch]
      -- ^ One branch per constructor.
  , spHidden   :: [String]
      -- ^ The variables that the user cannot refer to
      --   ('giOutOfScope') and that the right-hand sides use.
  }

-- | The variable eliminated by the recursor.
data SplitTarget
  = SplitVar String
      -- ^ A variable of the context, i.e. a pattern of the clause.
  | SplitArg Int [Hiding]
      -- ^ The @k@-th argument of the goal (counting the implicit ones),
      --   given the visibilities of all of them: the answer is
      --   @λ x₁ … xₙ → D.rec … xₖ@, and the arguments must be introduced as
      --   patterns first.

-- | The clause of a constructor.
data SplitBranch = SplitBranch
  { sbCtor   :: String
      -- ^ Name of the constructor.
  , sbFields :: [(String, Hiding, Bool)]
      -- ^ For each field: a suggested name, its visibility, and whether
      --   the right-hand side uses it.
  , sbRHS    :: ClauseNames -> String
      -- ^ The right-hand side, given the names bound by the clause.
  }

-- | The names bound by a clause produced by Agda's case split.
data ClauseNames = ClauseNames
  { cnFields :: [Maybe String]
      -- ^ The name of each field of the constructor, if bound.
  , cnArgs   :: Maybe [Maybe String]
      -- ^ The explicit arguments of the clause, for recursive calls: a name,
      --   or 'Nothing' at the position of the split variable.  'Nothing' if
      --   some argument is not a variable.
  , cnUsed   :: [String]
      -- ^ All the names bound by the clause.
  , cnParams :: [Maybe String]
      -- ^ For 'SplitArg': the names of the introduced arguments, if bound
      --   by the clause (implicit ones are not).
  , cnHidden :: [(String, String)]
      -- ^ The hidden variables made visible by the clause (@{x = y}@): name
      --   of the argument and of the variable, passed to the recursive calls.
  }

-- | A case split, if the answer is a recursor fully applied to a variable
--   of the context, or to one of its own arguments.
canonicalSplit
  :: GoalInfo  -- ^ Information about the goal.
  -> [CDecl]   -- ^ The context sent to Canonical, to recover the recursors.
  -> String    -- ^ Name of the function containing the hole, for recursive calls.
  -> CExpr     -- ^ The answer.
  -> Maybe Split
canonicalSplit info ctx self (CExpr ps _ (CSpine h as)) = do
  ri <- Map.lookup h (eRecs env)
  let (np, k, total) = recShape ri
  guard (length as == total)
  CExpr [] _ (CSpine x []) : _ <- Just (reverse as)
  target <- case elemIndex x (map name ps) of
    Just i -> Just (SplitArg i (take (length ps) (goalHid ++ repeat NotHidden)))
    Nothing | null ps, x `elem` giNames info
            , x `notElem` giOutOfScope info        -> Just (SplitVar x)
    _                                              -> Nothing
  let minors = take k (drop (np + 2) as)
  -- The recursors inside the branches are printed as pattern-matching lambdas.
  guard $ not $ or [ nestedIH env body | (br, m) <- zip (riBranches ri) minors
                                       , let (_, _, body, _) = branchParts env br m ]
  return Split
    { spTarget   = target
    , spBranches = zipWith (splitBranch env (map name ps) x np) (riBranches ri) minors
    , spHidden   = nub [ h | (br, m) <- zip (riBranches ri) minors
                           , let (_, _, body, env2) = branchParts env br m
                           , h <- outOfScopeIn env2 body ]
    }
  where
    env     = initEnv False info ctx self
    goalHid = maybe [] (map pHiding) (lookupSig info "Goal")

-- | The clause of a constructor, from its minor premise.
--
--   In the right-hand side, the split variable stands for the constructor
--   applied to its explicit fields, and the induction hypotheses become
--   recursive calls.
splitBranch :: Env -> [String] -> String -> Int -> Branch -> CExpr -> SplitBranch
splitBranch env ps x np br@(Branch c _ _) m = SplitBranch c fields rhs
  where
    (fps, pairs, body, env2) = branchParts env br m
    fields = zipWith (\ f hid -> (stripFresh (name f), hid, occurs env2 (name f) body))
                     fps (drop np (sigHidings env c) ++ repeat NotHidden)
    rhs cn = docText (arg env3 body)
      where
        binds = [ (name f, Local n) | (f, Just n) <- zip fps (cnFields cn) ]
             ++ [ (p, Local (fromMaybe "_" n)) | (p, n) <- zip ps (cnParams cn ++ repeat Nothing) ]
        calls = case cnArgs cn of
          Just cargs -> [ (ih, Call imps cargs f) | (ih, f) <- pairs ]
          Nothing    -> [ (ih, IH f)         | (ih, f) <- pairs ]
        imps  = [ "{" ++ a ++ " = " ++ v ++ "}" | (a, v) <- cnHidden cn ]
        ctorE = named (globalName env c) [ atom n | ((_, NotHidden, _), Just n) <- zip fields (cnFields cn) ]
        env3  = env2
          { eBound = Map.insert x (Local (atP 3 ctorE)) $
                       Map.union (Map.fromList (binds ++ calls)) (eBound env2)
          , eUsed  = Set.union (Set.fromList (cnUsed cn)) (eUsed env2)
          }
