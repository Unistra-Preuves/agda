-- | Printing of Canonical's answers in Agda syntax.
--
--   * Implicit arguments of applications are omitted: Agda infers them.
--
--   * Implicit binders (of λs and patterns) are kept, in braces, only when
--     they are used in the printed term.
--
--   * @Pi@, @Pi.mk@ and @Pi.f@ (see "Agda.Canonical.Builtin") are printed
--     back as Π-types, λs and applications.
--
--   * Recursors @D.rec@ (see "Agda.Canonical.Recursor") become
--     pattern-matching lambdas @λ { c₁ xs → … ; … }@.  Since these are not
--     recursive, an induction hypothesis used in a branch is printed as a
--     recursive call to the function containing the hole: the result then
--     reads as the clauses to write rather than as a valid term.
--
--   * The suffixes added by 'Agda.Canonical.Utils.freshString' are removed,
--     and primes are added to avoid shadowing a name in scope.

module Agda.Canonical.FromCanonical
  ( cexprToAgda
  ) where

import Data.List (elemIndex, intercalate, isSuffixOf)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set

import Agda.Canonical.Types
import Agda.Syntax.Common (Hiding (..))

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
  if np < 0 || ni < 0 then Nothing else Just (RecInfo np ni brs)
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
      -- ^ An induction hypothesis on the given field (Canonical name).

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
  Just (Local _) -> as
  Just (IH f)    -> [CExpr [] [] (CSpine f as)]
  Nothing -> case (h, as) of
    ("Type", [_])          -> as
    ("ß", [_])             -> as
    ("Pi", [_, _, a, b])   -> [a, b]
    ("Pi.mk", _ : _ : _ : _ : rest) -> rest
    ("Pi.f",  _ : _ : _ : _ : rest) -> rest
    _ | Just ri <- Map.lookup h (eRecs env)
      , let (np, k, total) = recShape ri
      , length as >= total
      -> take k (drop (np + 2) as) ++ drop (total - 1) as
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
  :: GoalInfo  -- ^ Information about the goal.
  -> [CDecl]   -- ^ The context sent to Canonical, to recover the recursors.
  -> String    -- ^ Name of the function containing the hole, for recursive calls.
  -> CExpr     -- ^ The answer.
  -> String
cexprToAgda info ctx self e = docText (expr env goalHid e)
  where
    env = Env { eInfo  = info
              , eRecs  = recInfos ctx
              , eSelf  = self
              , eBound = Map.empty
              , eUsed  = Set.fromList (giNames info ++ Map.keys (giGlobals info))
              , eFresh = 0 }
    goalHid = maybe [] (map pHiding) (lookupSig info "Goal")

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
  Nothing        -> special h as
  where
    special "Type" [l] = setDoc env "Set" l
    special "ß"    [l] = setDoc env "SSet" l
    special "Pi" [_, _, a, b] = piDoc env a b
    special "Pi.mk" (_ : _ : _ : _ : f : rest) = applyTo env f rest
    special "Pi.f"  (_ : _ : _ : _ : p : rest) = applyTo env p rest
    special _ _
      | Just ri <- Map.lookup h (eRecs env), Just d <- recDoc env ri as = d
    special _ _ = named shown (map (arg env) (visibleArgs env h as))
    shown | Map.member h (giGlobals (eInfo env)) = h
          | otherwise                            = stripFresh h

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

-- | @D.rec l pars motive minors idx major extra@ is printed as
--   @(λ { c fs → … ; … }) major extra@, or 'Nothing' if it is partially applied.
recDoc :: Env -> RecInfo -> [CExpr] -> Maybe Doc
recDoc env ri as = case drop (total - 1) as of
  major : extra -> Just (app patlam (map (arg env) (major : extra)))
  []            -> Nothing
  where
    (np, k, total) = recShape ri
    minors = take k (drop (np + 2) as)
    patlam
      | k == 0    = Doc 0 "λ ()"
      | otherwise = Doc 0 ("λ { " ++ intercalate " ; "
                             (zipWith (branchDoc env np) (riBranches ri) minors) ++ " }")

-- | A clause @c fs → body@ of the pattern-matching lambda, from a minor premise.
branchDoc :: Env -> Int -> Branch -> CExpr -> String
branchDoc env np (Branch c nf ihs) m =
  atP 3 pat ++ " → " ++ docText (arg env3 body)
  where
    (CExpr mps _ msp, env1) = etaTo (nf + length ihs) m env
    (bps, more) = splitAt (nf + length ihs) mps
    (fps, ips)  = splitAt nf bps
    body  = CExpr more [] msp
    pairs = [ (name ih, name (fps !! i)) | (ih, i) <- zip ips ihs ]
    env2  = env1 { eBound = foldr (\(ih, f) -> Map.insert ih (IH f)) (eBound env1) pairs }
    used x = occurs env2 x body   -- a field counts as used through its IH
    hs    = drop np (sigHidings env c)
    (pstrs, env3) = binders env2 used (zip (map name fps) (hs ++ repeat NotHidden))
    pat | any ((`elem` ["{", "⦃"]) . take 1) pstrs = app (atom c) (map atom pstrs)
        | otherwise                                = named c (map atom pstrs)
