module Agda.Canonical.Types where


import GHC.Generics (Generic)
import Data.Aeson
import Data.List (intercalate)
import Agda.Utils.Lens (set)
import Agda.Utils.Impossible (__IMPOSSIBLE__)

data CRule = CRule
  { rlhs :: CSpine,
    rrhs :: CSpine
  }
  deriving (Generic)

data CSpine = CSpine
  { shead :: String,
    sargs :: [CTerm]
  }
  deriving (Generic)


data CTerm = CTerm
  { thead :: [String],
    targs :: CSpine
  }
  deriving (Generic)


data CType = CType
  { bindings :: [(String, Maybe CType)],
    lets :: [(String, Maybe CType, [CRule])],
    codom :: CSpine
  }
  deriving (Generic)

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

  -- show (CSpine {shead = sh, sargs = sa}) =
  --   case sa of
  --     [] -> sh
  --     _ -> "(" ++ sh ++ aux sa ++ ")"
  --   where
  --     aux :: [CTerm] -> String
  --     aux [] = ""
  --     aux [t] = " " ++ show t
  --     aux (t : l) = " " ++ show t ++ aux l

instance FromJSON CSpine where
  parseJSON = withObject "CSpine" $
    \v ->
      CSpine
        <$> v .: "shead"
        <*> v .: "sargs"

instance ToJSON CSpine where
  toEncoding = genericToEncoding defaultOptions

instance FromJSON CRule where
  parseJSON = withObject "CRule" $
    \v ->
      CRule
        <$> v .: "rlhs"
        <*> v .: "rrhs"

instance ToJSON CRule where
  toEncoding = genericToEncoding defaultOptions


instance Show CTerm where
  showsPrec p (CTerm th ta) =
    let lamPrec = 0  in
    showParen (p > lamPrec && not (null th)) $
      case th of
        [] -> showsPrec p ta
        _ -> showString "λ "
             . showString (unwords th)
             . showString " → "
             . showsPrec lamPrec ta

{-
  show (CTerm {thead = th, targs = ta}) =
    case th of
      [] -> show ta
      _ -> "(" ++ pplbd th ++ show ta ++ ")"
    where
      pplbd :: [String] -> String
      pplbd [] = ""
      pplbd b = "λ " ++ aux b ++ " → "
        where
          aux :: [String] -> String
          aux [] = ""
          aux [s] = s
          aux (s : l) = s ++ ", " ++ aux l
-}
instance FromJSON CTerm where
  parseJSON = withObject "CTerm" $
    \v ->
      CTerm
        <$> v .: "thead"
        <*> v .: "targs"

instance ToJSON CTerm where
  toEncoding = genericToEncoding defaultOptions

instance Show CRule where
  show CRule{rlhs , rrhs} = show rlhs ++ " ⤇ " ++ show rrhs


instance Show CType where
  show (CType {bindings = bds, lets = lts, codom = sp}) = ppbds bds ++ pplts lts ++ show sp
    where
      ppbds :: [(String, Maybe CType)] -> String
      ppbds [] = ""
      ppbds b = "Π" ++ aux b ++ ". "
        where
          aux :: [(String, Maybe CType)] -> String
          aux [] = ""
          aux [(s, t)] = "(" ++ s ++ " : " ++ show t ++ ")"
          aux ((s, t) : l) = "(" ++ s ++ " : " ++ show t ++ "), " ++ aux l

      pplts :: [(String, Maybe CType, [CRule])] -> String
      pplts [] = ""
      pplts b = "let " ++ aux b ++ ". "
        where
          auxaux :: [CRule] -> String
          auxaux [] = ""
          auxaux l = "{" ++ auxauxaux l ++ "}"
            where
              auxauxaux :: [CRule] -> String
              auxauxaux rs = case rs of
                [] -> __IMPOSSIBLE__
                [r] -> show r
                r : rs -> show r ++ ", " ++ auxauxaux rs

          aux :: [(String, Maybe CType, [CRule])] -> String
          aux [] = ""
          aux [(s, t, rs)] = "(" ++ s ++ " : " ++ show t ++ " " ++ (auxaux rs) ++ ")"
          aux ((s, t, rs) : l) = "(" ++ s ++ " : " ++ show t ++ " " ++ auxaux rs ++ "), " ++ aux l

instance ToJSON CType where
  toEncoding = genericToEncoding defaultOptions

instance FromJSON CType where
  parseJSON = withObject "CType" $
    \v ->
      CType
        <$> v .: "bindings"
        <*> v .: "lets"
        <*> v .: "codom"

data CanonicalResult
  = CanonicalExpr String
  | CanonicalList [(Int, String)]
  | CanonicalNoResult
  deriving (Generic)

dummyCSpine :: CSpine
dummyCSpine = CSpine {
    shead = "",
    sargs = []
  }

dummyCTerm :: CTerm
dummyCTerm = CTerm {
    thead = [],
    targs = dummyCSpine
  }

dummyCType :: CType
dummyCType = CType {
    bindings = [],
    lets = [],
    codom = dummyCSpine
  }

simpleSpine :: String -> CSpine
simpleSpine s = CSpine {
      shead = s,
      sargs = []
}

simpleTerm :: String -> CTerm
simpleTerm s =
  CTerm {
    thead = [],
    targs = simpleSpine s
  }

simpleType :: String -> CType
simpleType s = CType {
  bindings = [],
  lets = [],
  codom = simpleSpine s
}

pathSpine :: CSpine
pathSpine =
  CSpine {
    shead = "_≡_",
    sargs = [simpleTerm "ℓ", simpleTerm "A", simpleTerm "x", simpleTerm "y"]
  }

mpType :: CType
mpType =
  let tS = simpleType "Set ℓ"
      tI = simpleType "I"
      tA = simpleType "A"
      tL = simpleType "Level"
      tp = CType {
          bindings = [ ("i", Just tI)],
          lets = [],
          codom = simpleSpine "A"
        }
      codom = pathSpine  in
  CType {
    bindings = [("ℓ", Just tL), ("A", Just tS), ("p", Just tp), ("x", Just tA), ("y", Just tA)],
    lets = [],
    codom
  }


topathType :: CType
topathType =
  let tS = simpleType "Set ℓ"
      tI = simpleType "I"
      tA = simpleType "A"
      tL = simpleType "Level"
      tP = CType {
          bindings = [],
          lets = [],
          codom = pathSpine
        }
  in
  CType{
    bindings = [("ℓ", Just tL), ("A", Just tS), ("x", Just tA), ("y", Just tA), ("p", Just tP), ("i", Just tI)],
    lets = [],
    codom = simpleSpine "A"
  }

mpSpine :: CSpine
mpSpine  = CSpine {
             shead = ".mp",
             sargs = [simpleTerm "ℓ", simpleTerm "A", simpleTerm "p", simpleTerm "x", simpleTerm "y"]
           }

mpTerm :: CTerm
mpTerm  = CTerm {
            thead = [],
            targs = mpSpine
          }

toPathRule1 :: CRule
toPathRule1 =
  let rlhs = CSpine {
              shead = ".path",
              sargs = [simpleTerm "ℓ", simpleTerm "A", simpleTerm "x", simpleTerm "y", mpTerm ]
            }
      rrhs = simpleSpine "p"
  in
  CRule {
      rlhs,
      rrhs
  }


toPathRule2 :: CRule
toPathRule2 =
  let rlhs = CSpine {
              shead = ".path",
              sargs = [simpleTerm "ℓ", simpleTerm "A", simpleTerm "x", simpleTerm "y", mpTerm, simpleTerm "i0"]
            }
      rrhs = simpleSpine "x"
  in
  CRule {
      rlhs,
      rrhs
  }


toPathRule3 :: CRule
toPathRule3 =
  let rlhs = CSpine {
              shead = ".path",
              sargs = [simpleTerm "ℓ", simpleTerm "A", simpleTerm "x", simpleTerm "y", mpTerm, simpleTerm "i1"]
            }
      rrhs = simpleSpine "y"
  in
  CRule {
      rlhs,
      rrhs
  }
