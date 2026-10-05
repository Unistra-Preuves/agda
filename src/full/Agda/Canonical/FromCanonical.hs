module Agda.Canonical.FromCanonical (cexprToAgda) where

import Data.List (elemIndex, intercalate, isSuffixOf)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set

import Agda.Canonical.Types
import Agda.Syntax.Common (Hiding (..))

{-
  Post-traitement du résultat de Canonical : impression en syntaxe Agda.

  - Les arguments implicites des applications sont omis (Agda les infère).
  - Les lieurs implicites (λ et motifs) ne sont gardés, entre accolades,
    que s'ils sont utilisés dans le corps.
  - Pi / Pi.mk / Pi.f sont ramenés à →, λ et l'application.
  - Les récurseurs D.rec deviennent des λ { … } par filtrage ; une hypothèse
    d'induction utilisée devient un appel récursif à la fonction du but
    (ce qui n'est plus un terme Agda valide : il se lit comme des clauses).
-}

---- Documents ----

-- | Texte imprimé et sa précédence :
--   0 = λ / Π, 1 = opérateur mixfix, 2 = application, 3 = atome.
data Doc = Doc { docPrec :: Int, docText :: String }

atom :: String -> Doc
atom = Doc 3

-- | Texte du document dans une position demandant au moins la précédence n.
atP :: Int -> Doc -> String
atP n (Doc p s)
  | p >= n    = s
  | otherwise = "(" ++ s ++ ")"

app :: Doc -> [Doc] -> Doc
app d [] = d
app d ds = Doc 2 (unwords (map (atP 3) (d : ds)))

lam :: [String] -> Doc -> Doc
lam [] d = d
lam bs d = Doc 0 ("λ " ++ unwords bs ++ " → " ++ docText d)

-- | Application d'un nom, en notation mixfix si elle est saturée.
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

wrap :: Hiding -> String -> String
wrap NotHidden  s = s
wrap Hidden     s = "{" ++ s ++ "}"
wrap Instance{} s = "⦃ " ++ s ++ " ⦄"

---- Récurseurs ----

data Branch = Branch
  { brCtor   :: String
  , brFields :: Int
  , brIhs    :: [Int]  -- pour chaque hypothèse d'induction, l'indice de son champ
  }

data RecInfo = RecInfo { riPars, riIdx :: Int, riBranches :: [Branch] }

-- | Retrouve la forme des récurseurs générés (cf. mkRecursor) à partir du contexte.
recInfos :: [CDecl] -> Map String RecInfo
recInfos ds = Map.fromList
  [ (name d, ri) | d <- ds, ".rec" `isSuffixOf` name d, Just ri <- [recInfo d] ]

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

-- | Nombre de paramètres, de constructeurs, et arité totale du récurseur.
recShape :: RecInfo -> (Int, Int, Int)
recShape ri = (np, k, np + k + riIdx ri + 3)
  where np = riPars ri
        k  = length (riBranches ri)

---- Environnement ----

data Bound
  = Local String  -- variable liée, avec son nom Agda
  | IH String     -- hypothèse d'induction sur le champ donné (nom Canonical)

data Env = Env
  { eInfo  :: GoalInfo
  , eRecs  :: Map String RecInfo
  , eSelf  :: String             -- nom des appels récursifs
  , eBound :: Map String Bound
  , eUsed  :: Set String         -- noms Agda déjà pris
  , eFresh :: Int
  }

-- | Nom lisible : on retire le suffixe ajouté par freshString.
stripFresh :: String -> String
stripFresh s = case takeWhile (/= '.') s of
  ""  -> "x"
  "_" -> "x"
  b   -> b

bind :: String -> Env -> (String, Env)
bind x env = (x', env { eBound = Map.insert x (Local x') (eBound env)
                      , eUsed  = Set.insert x' (eUsed env) })
  where
    x' = case filter (`Set.notMember` eUsed env) (iterate (++ "'") (stripFresh x)) of
      n : _ -> n
      []    -> stripFresh x

freshVar :: Env -> (String, Env)
freshVar env = ("x.η" ++ show (eFresh env), env { eFresh = eFresh env + 1 })

-- | Lieurs : explicites toujours (« _ » si inutilisés), implicites seulement
--   s'ils sont utilisés ou qu'un implicite suivant (avant le prochain explicite) l'est.
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

-- | Arguments effectivement imprimés pour la tête h (cf. spineDoc).
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

sigHidings :: Env -> String -> [Hiding]
sigHidings env h = maybe [] (map pHiding) (lookupSig (eInfo env) h)

-- | Occurrence de x dans ce qui sera imprimé (les arguments implicites omis ne comptent pas).
occurs :: Env -> String -> CExpr -> Bool
occurs env x (CExpr _ _ sp) = occursS env x sp

occursS :: Env -> String -> CSpine -> Bool
occursS env x (CSpine h as) = h == x || any (occurs env x) (visibleArgs env h as)

-- | Complète un CExpr à n paramètres (η-expansion).
etaTo :: Int -> CExpr -> Env -> (CExpr, Env)
etaTo n ce@(CExpr ps ls (CSpine h as)) env
  | length ps >= n = (ce, env)
  | otherwise      = (CExpr (ps ++ map (\x -> CDecl x Nothing []) xs) ls
                            (CSpine h (as ++ map simpleExpr xs)), env')
  where
    (xs, env') = foldr (\_ (acc, e) -> let (x, e1) = freshVar e in (x : acc, e1))
                       ([], env) [1 .. n - length ps]

---- Impression ----

{-
  Imprime en syntaxe Agda la réponse de Canonical au but.
  `lets` est le contexte envoyé à Canonical (pour retrouver les récurseurs),
  `self` le nom de la fonction contenant le trou (appels récursifs).
-}
cexprToAgda :: GoalInfo -> [CDecl] -> String -> CExpr -> String
cexprToAgda info ctx self e = docText (expr env goalHid e)
  where
    env = Env { eInfo  = info
              , eRecs  = recInfos ctx
              , eSelf  = self
              , eBound = Map.empty
              , eUsed  = Set.fromList (giNames info ++ Map.keys (giGlobals info))
              , eFresh = 0 }
    goalHid = maybe [] (map pHiding) (lookupSig info "Goal")

-- | Un CExpr, dont les paramètres ont les visibilités données (explicites par défaut).
expr :: Env -> [Hiding] -> CExpr -> Doc
expr env hs (CExpr ps _ sp) = lam bs (spineDoc env' sp)
  where (bs, env') = binders env (\x -> occursS env x sp) (zip (map name ps) (hs ++ repeat NotHidden))

arg :: Env -> CExpr -> Doc
arg env = expr env []

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

applyTo :: Env -> CExpr -> [CExpr] -> Doc
applyTo env (CExpr [] _ (CSpine g gs)) rest = spineDoc env (CSpine g (gs ++ rest))
applyTo env f rest = app (arg env f) (map (arg env) rest)

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

-- | Pi u v A B : (x : A) → B x, ou A → B si x n'apparaît pas.
piDoc :: Env -> CExpr -> CExpr -> Doc
piDoc env a b = case b of
  CExpr (x : rest) _ sp
    | occurs env (name x) body ->
        let (x', env') = bind (name x) env
        in Doc 0 ("(" ++ x' ++ " : " ++ docText (arg env a) ++ ") → " ++ docText (arg env' body))
    | otherwise -> Doc 0 (atP 1 (arg env a) ++ " → " ++ docText (arg env body))
    where body = CExpr rest [] sp
  CExpr [] _ _ -> let (b', env') = etaTo 1 b env in piDoc env' a b'

-- | D.rec {l} {pars} motive minors {idx} major extra  ~>  (λ { c fs → … }) major extra
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
    used x = occurs env2 x body   -- un champ sous une ih utilisée compte via IH
    hs    = drop np (sigHidings env c)
    (pstrs, env3) = binders env2 used (zip (map name fps) (hs ++ repeat NotHidden))
    pat | any ((`elem` ["{", "⦃"]) . take 1) pstrs = app (atom c) (map atom pstrs)
        | otherwise                                = named c (map atom pstrs)
