module Agda.Canonical.Types where


import GHC.Generics (Generic)
import Data.Aeson

data Spine = Spine
  { shead :: String,
    sargs :: [Term]
  }
  deriving (Generic)

instance Show Spine where
  show (Spine {shead = sh, sargs = sa}) = sh ++ aux sa
    where
      aux :: [Term] -> String
      aux [] = ""
      aux [t] = " " ++ "(" ++ show t ++ ")"
      aux (t : l) = "(" ++ show t ++ ") " ++ aux l

instance FromJSON Spine where
  parseJSON = withObject "Spine" $
    \v ->
      Spine
        <$> v .: "shead"
        <*> v .: "sargs"

instance ToJSON Spine where
  toEncoding = genericToEncoding defaultOptions

data Term = Term
  { thead :: [String],
    targs :: Spine
  }
  deriving (Generic)

instance Show Term where
  show (Term {thead = th, targs = ta}) = pplbd th ++ show ta
    where
      pplbd :: [String] -> String
      pplbd [] = ""
      pplbd b = "λ " ++ aux b ++ ". "
        where
          aux :: [String] -> String
          aux [] = ""
          aux [s] = s
          aux (s : l) = s ++ ", " ++ aux l

instance FromJSON Term where
  parseJSON = withObject "Term" $
    \v ->
      Term
        <$> v .: "thead"
        <*> v .: "targs"

instance ToJSON Term where
  toEncoding = genericToEncoding defaultOptions

data Type = Type
  { bindings :: [(String, Type)],
    codom :: Spine
  }
  deriving (Generic)

instance Show Type where
  show (Type {bindings = bds, codom = sp}) = ppbds bds ++ show sp
    where
      ppbds :: [(String, Type)] -> String
      ppbds [] = ""
      ppbds b = "Π" ++ aux b ++ ". "
        where
          aux :: [(String, Type)] -> String
          aux [] = ""
          aux [(s, t)] = "(" ++ s ++ " : " ++ show t ++ ")"
          aux ((s, t) : l) = "(" ++ s ++ " : " ++ show t ++ "), " ++ aux l

instance ToJSON Type where
  toEncoding = genericToEncoding defaultOptions

instance FromJSON Type where
  parseJSON = withObject "Typ" $
    \v ->
      Type
        <$> v .: "bindings"
        <*> v .: "codom"

data CanonicalResult
  = CanonicalExpr String
  | CanonicalList [(Int, String)]
  | CanonicalNoResult
  deriving (Generic)
