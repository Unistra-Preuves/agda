module Agda.Canonical.Types where


import GHC.Generics (Generic)
import Data.Aeson

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
    lets :: [(String, Maybe CType)],
    codom :: CSpine
  }
  deriving (Generic)

instance Show CSpine where
  show (CSpine {shead = sh, sargs = sa}) =
    case sa of
      [] -> sh
      _ -> "(" ++ sh ++ aux sa ++ ")"
    where
      aux :: [CTerm] -> String
      aux [] = ""
      aux [t] = " " ++ show t
      aux (t : l) = " " ++ show t ++ aux l

instance FromJSON CSpine where
  parseJSON = withObject "CSpine" $
    \v ->
      CSpine
        <$> v .: "shead"
        <*> v .: "sargs"

instance ToJSON CSpine where
  toEncoding = genericToEncoding defaultOptions


instance Show CTerm where
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

instance FromJSON CTerm where
  parseJSON = withObject "CTerm" $
    \v ->
      CTerm
        <$> v .: "thead"
        <*> v .: "targs"

instance ToJSON CTerm where
  toEncoding = genericToEncoding defaultOptions


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

      pplts :: [(String, Maybe CType)] -> String
      pplts [] = ""
      pplts b = "let " ++ aux b ++ ". "
        where
          aux :: [(String, Maybe CType)] -> String
          aux [] = ""
          aux [(s, t)] = "(" ++ s ++ " : " ++ show t ++ ")"
          aux ((s, t) : l) = "(" ++ s ++ " : " ++ show t ++ "), " ++ aux l


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


