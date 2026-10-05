module Agda.Canonical.Types where


import Data.Aeson
import Data.Char (isDigit, isSpace)
import Data.List (dropWhileEnd, stripPrefix)
import Data.Map (Map)
import Data.Map qualified as Map
import GHC.Generics (Generic)
import Text.Read (readMaybe)

import Agda.Syntax.Common (Hiding)
import Agda.Utils.Impossible (__IMPOSSIBLE__)

{-
  A Canonical declaration represents a typing judgement (name : typ).

  The type is optionnal.
  If it's not specified, Canonical will not try to type the the symbol when using it.

  If the declaration belongs to the field params of a Canonical expression,
  Canonical interprets the equations as constraints.

  If it belongs to the field lets, Canonical interprets equations as definitions.
  eg.
    not : Bool -> Bool
    not True = False
    not False =  True

    CDecl {
      name = "not",
      typ = Just (Bool -> Bool),
      equations = [not True = False;
                   not False = True]
    }
-}
data CDecl = CDecl {
    name :: String,
    typ  :: Maybe CExpr,
    equations :: [CEquation]
  }
  deriving (Generic)

{-
  A Canonical Equation is two spines representing the two handsigns of the equations,
  together with a Boolean indicating if the equation is a redex.

  eg.
    In the previous example, not True = False :
    CEquation {
        lhs = not True,
        rhs = False,
        is_redex = True
    }
-}

data CEquation = CEquation
  { lhs :: CSpine,
    rhs :: CSpine,
    is_redex :: Bool
  }
  deriving (Generic)

{-
  A Canonical expression is used to represent both types and terms.
  When viewed as types, an expression should be interpreted as
  let `lets` in Pi `params`. `spine`

  Canonical will return an expression as a result.
  The `lets` field will always be empty.
  The returned expression should be viewed as
  lambda `params`. spine
-}

data CExpr = CExpr
  { params :: [CDecl],
    lets :: [CDecl],
    spine :: CSpine
  }
  deriving (Generic)

{-
  A Canonical spine is a head symbol applied to multiples expressions.
-}
data CSpine = CSpine
  { head :: String,
    args :: [CExpr]
  }
  deriving (Generic)

---- Pretty printing functions and JSON support ----

instance FromJSON CDecl where
  parseJSON = withObject "CDecl" $
    \v ->
      CDecl
        <$> v .: "name"
        <*> v .: "typ"
        <*> v .: "equations"

instance ToJSON CDecl where
  toEncoding = genericToEncoding defaultOptions

instance FromJSON CSpine where
  parseJSON = withObject "CSpine" $
    \v ->
      CSpine
        <$> v .: "head"
        <*> v .: "args"

instance ToJSON CSpine where
  toEncoding = genericToEncoding defaultOptions


instance FromJSON CEquation where
  parseJSON = withObject "CEquation" $
    \v ->
      CEquation
        <$> v .: "lhs"
        <*> v .: "rhs"
        <*> v .: "is_redex"

instance ToJSON CEquation where
  toEncoding = genericToEncoding defaultOptions

instance FromJSON CExpr where
  parseJSON = withObject "CExpr" $
    \v ->
      CExpr
        <$> v .: "params"
        <*> v .: "lets"
        <*> v .: "spine"

instance ToJSON CExpr where
  toEncoding = genericToEncoding defaultOptions


-- instance Pretty CSpine where
--   pretty = text . show

instance Show CSpine where
  showsPrec p (CSpine sh sa) =
    let appPrec = 10 in
    showParen (p > appPrec && not (null sa)) $
      showString sh .
      foldr (.)
        id
        [ showChar ' ' . showsPrec (appPrec + 1) t
        | t <- sa
        ]
instance Show CEquation where
  showsPrec p CEquation{lhs , rhs} = showsPrec p lhs . showString " ⤇ " . showsPrec p rhs

instance Show CExpr where
  showsPrec p CExpr{params, lets, spine} =
    case params of
      [] -> showsPrec p spine
      _ -> showParen (p > 0) $
        showParams params . showsPrec 1 spine
          where
            showParams :: [CDecl] -> ShowS
            showParams [] = id
            showParams (d : dl) = shows d . showString " -> " . showParams dl

instance Show CDecl where
  show CDecl{name, typ, equations} =
    if name /= "Goal"
      then
        let typ' = maybe "_" show typ
        in "(" ++ name ++ " : " ++ typ' ++ ")" ++ showEq equations
      else
        case typ of
          Nothing -> "--- Goal :\n_"
          Just (CExpr params lets spine) ->
            showlet lets ++ showcons equations ++ "--- Goal :\n" ++ show (CExpr params lets spine)
    where
      showlet :: [CDecl] -> String
      showlet [] = ""
      showlet dl = "--- Context :\n" ++ showdecl dl ++ "\n\n"
        where
          showdecl :: [CDecl] -> String
          showdecl [] = __IMPOSSIBLE__
          showdecl [d] = show d
          showdecl (d:dl) = show d ++ "\n" ++ showdecl dl

      showEq :: [CEquation] -> String
      showEq [] = ""
      showEq l = "{" ++ aux l ++ "}"
        where
          aux :: [CEquation] -> String
          aux [] = __IMPOSSIBLE__
          aux [d] = show d
          aux (d : l) = show d ++ "; " ++ aux l

      showcons :: [CEquation] -> String
      showcons [] = ""
      showcons el = "--- Constraints :\n" ++ aux el ++ "\n"
        where
          aux :: [CEquation] -> String
          aux [] = ""
          aux (e : el) = show e ++ "\n" ++ aux el

---- END ----
data Param = Param { pArity :: Int, pHiding :: Hiding } deriving Show
type Sig  = [Param]
type Seen = Map String Sig      -- ex-ald : symboles déjà vus -> signature

data GoalInfo = GoalInfo
  { giGlobals :: Map String Sig  -- datatypes, constructeurs, Pi, Level, ...
  , giLocals  :: Map String Sig  -- variables du contexte et "Goal"
  , giNames   :: [String]        -- noms liés, du plus récent au plus ancien
  }

lookupSig :: GoalInfo -> String -> Maybe Sig
lookupSig gi s = Map.lookup s (giLocals gi) `orElse` Map.lookup s (giGlobals gi)
  where orElse (Just x) _ = Just x
        orElse Nothing  y = y


---- Options ----

{-
  Options de C-c C-g, données dans le trou, dans le format de la tactique Lean :

    {! [timeout] [(count := n)] [[lem₁, lem₂, …]] !}

  eg. {! 10 (count := 3) [+-comm, cong] !}
  La liste de lemmes vient en dernier : un nom comme [] peut y figurer.
-}
data CanonicalOptions = CanonicalOptions
  { optTimeout :: Int       -- en secondes
  , optCount   :: Int       -- nombre de solutions demandées
  , optLemmas  :: [String]  -- noms à ajouter au contexte de Canonical
  }

defaultCanonicalOptions :: CanonicalOptions
defaultCanonicalOptions = CanonicalOptions { optTimeout = 5, optCount = 1, optLemmas = [] }

canonicalUsage :: String
canonicalUsage = "Usage : {! [timeout] [(count := n)] [[lem₁, lem₂, …]] !}"

parseCanonicalOptions :: String -> Either String CanonicalOptions
parseCanonicalOptions = go defaultCanonicalOptions . trim
  where
    go o "" = Right o
    go o s@(c : _) | isDigit c =
      let (n, r) = span isDigit s in go o { optTimeout = read n } (trim r)
    go o ('(' : r) = case break (== ')') r of
      (inside, ')' : r') -> config o inside >>= \o' -> go o' (trim r')
      _                  -> Left "parenthèse fermante manquante"
    go o ('[' : r) = case break (== ']') (reverse r) of
      (after, ']' : inside) | all isSpace after ->
        Right o { optLemmas = optLemmas o ++ lemmaNames (reverse inside) }
      _ -> Left "la liste de lemmes doit être fermée par ] et venir en dernier"
    go _ s@(c : _) | c `elem` ("+-" :: String) =
      Left ("option " ++ takeWhile (not . isSpace) s ++ " non supportée par la version Agda")
    go _ s = Left ("option invalide : " ++ takeWhile (not . isSpace) s)

    config o inside = case break (== ':') inside of
      (k, ':' : '=' : v) -> case (trim k, readMaybe (trim v)) of
        ("count",   Just n) | n > 0  -> Right o { optCount = n }
        ("timeout", Just n) | n >= 0 -> Right o { optTimeout = n }
        (key, _) | key `elem` ["count", "timeout"] -> Left ("valeur invalide pour l'option " ++ key)
                 | otherwise -> Left ("option inconnue : " ++ key)
      _ -> Left ("option invalide : (" ++ inside ++ ")")

    -- Séparateur « , » ; un nom Agda peut contenir une virgule (_,_), d'où la prudence.
    lemmaNames = concatMap splitWord . words
    splitWord w = case stripTrailingComma w of
      ""                                   -> []
      w' | ',' `elem` w', '_' `notElem` w' -> filter (not . null) (splitOn ',' w')
         | otherwise                       -> [w']
    stripTrailingComma w
      | w == ","                              = ""
      | Just w' <- stripSuffix "," w, w' /= "_" = w'
      | otherwise                             = w
    stripSuffix suf w = reverse <$> stripPrefix (reverse suf) (reverse w)
    splitOn c s = case break (== c) s of
      (a, _ : r) -> a : splitOn c r
      (a, [])    -> [a]
    trim = dropWhileEnd isSpace . dropWhile isSpace

data CanonicalResult
  = CanonicalExpr String
  | CanonicalList [(Int, String)]
  | CanonicalNoResult
  deriving (Generic)

dummyCSpine :: CSpine
dummyCSpine = CSpine {
    head = "",
    args = []
  }

dummyCExpr :: CExpr
dummyCExpr = CExpr {
    params = [],
    lets = [],
    spine = dummyCSpine
  }

typeDecl :: CDecl
typeDecl = CDecl {
    name = "Type",
    typ = Nothing,
    equations = []
  }


ssetDecl :: CDecl
ssetDecl = CDecl {
    name = "ß",
    typ = Nothing,
    equations = []
  }



simpleSpine :: String -> CSpine
simpleSpine s = CSpine {
      head = s,
      args = []
}


simpleExpr :: String -> CExpr
simpleExpr s = CExpr {
  params = [],
  lets = [],
  spine = simpleSpine s
}

---- Equations -----

levelMaxEqs :: [CEquation]
levelMaxEqs =
  [ -- lzero ⊔ x = x
    CEquation (CSpine "_⊔_" [lz, x]) (CSpine "x" []) True
    -- x ⊔ lzero = x
  , CEquation (CSpine "_⊔_" [x, lz]) (CSpine "x" []) True
    -- lsuc x ⊔ lsuc y = lsuc (x ⊔ y)
  , CEquation (CSpine "_⊔_" [ls x, ls y])
              (CSpine "lsuc" [CExpr [] [] (CSpine "_⊔_" [x, y])]) True
    -- x ⊔ x = x
  , CEquation (CSpine "_⊔_" [x, x]) (CSpine "x" []) True
  ]
  where
    x  = simpleExpr "x"
    y  = simpleExpr "y"
    lz = CExpr [] [] (CSpine "lzero" [])
    ls e = CExpr [] [] (CSpine "lsuc" [e])




eta1 :: String -> CExpr          -- λy. n y
eta1 n = CExpr [CDecl "y" Nothing []] [] (CSpine n [simpleExpr "y"])

typed :: String -> CExpr -> CDecl
typed n t = CDecl n (Just t) []

tyOf :: String -> CExpr
tyOf l = CExpr [] [] (CSpine "Type" [simpleExpr l])

piDecls :: [CDecl]
piDecls =
  [ CDecl "Pi" (Just $ CExpr hdr [] (CSpine "Type" [lmax])) []
  , CDecl "Pi.mk"
      (Just $ CExpr (hdr ++ [typed "f" fnT]) [] (CSpine "Pi" piHd)) []
  , CDecl "Pi.f"
      (Just $ CExpr (hdr ++ [typed "p" piT, typed "a" (simpleExpr "A")]) []
                    (CSpine "B" [simpleExpr "a"]))
      [ CEquation
          (CSpine "Pi.f" (lvls ++ [ simpleExpr "A", eta1 "B"
                                  , CExpr [] [] (CSpine "Pi.mk" (piHd ++ [eta1 "g"]))
                                  , simpleExpr "a" ]))
          (CSpine "g" [simpleExpr "a"]) True ]
  ]
  where
    lvls = [simpleExpr "u", simpleExpr "v"]
    piHd = lvls ++ [simpleExpr "A", eta1 "B"]
    hdr  = [ typed "u" (simpleExpr "Level"), typed "v" (simpleExpr "Level")
           , typed "A" (tyOf "u"), typed "B" famT ]
    famT = CExpr [typed "x" (simpleExpr "A")] [] (CSpine "Type" [simpleExpr "v"])
    fnT  = CExpr [typed "a" (simpleExpr "A")] [] (CSpine "B" [simpleExpr "a"])
    piT  = CExpr [] [] (CSpine "Pi" piHd)
    lmax = CExpr [] [] (CSpine "_⊔_" lvls)

