module Agda.Canonical.Types where


import GHC.Generics (Generic)
import Data.Aeson
import Data.List (intercalate)
import Agda.Utils.Lens (set)
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Interaction.Base (Interaction'(Cmd_constraints))

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

setDecl :: CDecl
setDecl = CDecl {
    name = "Set",
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


---- Cubical stuff for Canonical ----

pathSpine :: CSpine
pathSpine =
  let le = CExpr [] [] (CSpine "p" [simpleExpr  "i0"])
      re = CExpr [] [] (CSpine "p" [simpleExpr  "i1"])
  in
  CSpine {
    head = "_≡_",
    args = [simpleExpr "ℓ", simpleExpr "A", simpleExpr "x", simpleExpr "y"]
  }

mpExpr :: CExpr
mpExpr =
  let tS = CExpr [] [] (CSpine "Set" [simpleExpr "ℓ"])
      tI = simpleExpr "I"
      tA = simpleExpr "A"
      tL = simpleExpr "Level"
      tp = CExpr {
          params = [ CDecl "i" (Just tI) []],
          lets = [],
          spine = simpleSpine "A"
        }
      spine = pathSpine
      lhs1 = CSpine "p" [simpleExpr "i0"]
      lhs2 = CSpine "p" [simpleExpr "i1"]
      -- lhs1 = simpleSpine "x"
      -- lhs2 = simpleSpine "y"
      sx = simpleSpine "x"
      sy = simpleSpine "y"
  in
  CExpr {
    params = [CDecl "ℓ" (Just tL) [],
              CDecl "A" (Just tS) [],
              CDecl "x" (Just tA) [],
              CDecl "y" (Just tA) [],
              CDecl "p" (Just tp) [CEquation lhs1 sx True, CEquation lhs2 sy True]],
    lets = [],
    spine
  }

mpDecl :: CDecl
mpDecl = CDecl "mp" (Just mpExpr) []

dpExpr :: CExpr
dpExpr =
  let tS = CExpr [] [] (CSpine "Set" [simpleExpr "ℓ"])
      tI = simpleExpr "I"
      tA = simpleExpr "A"
      tL = simpleExpr "Level"
  in
  CExpr {
    params = [CDecl "ℓ" (Just tL) [],
              CDecl "A" (Just tS) [],
              CDecl "x" (Just tA) [],
              CDecl "y" (Just tA) [],
              CDecl "p" (Just $ CExpr [] [] pathSpine) [],
              CDecl "i" (Just tI) []],
    lets = [],
    spine = simpleSpine "A"
  }

dpDecl :: CDecl
dpDecl =
  let tA = simpleExpr "A"
      tL = simpleExpr "ℓ"
      tX = simpleExpr "x"
      tY = simpleExpr "y"
      tP = simpleExpr "p"
      tQ = simpleExpr "q"
      tI0 = simpleExpr "i0"
      tI1 = simpleExpr "i1"
      tMP = CExpr [] [] (CSpine "mp" [tL, tA, tX, tY, tQ])
      eq1lhs = CSpine "dp" [tL, tA, tX, tY, tP, tI0]
      eq2lhs = CSpine "dp" [tL, tA, tX, tY, tP, tI1]
      eq3lhs = CSpine "dp" [tL, tA, tX, tY, tMP]
      eq1 = CEquation eq1lhs (simpleSpine "x") True
      eq2 = CEquation eq2lhs (simpleSpine "y") True
      eq3 = CEquation eq3lhs (simpleSpine "q") True
  in
  CDecl "dp" (Just dpExpr) [eq1, eq2]

iDecl :: CDecl
iDecl = CDecl "I" Nothing []

i0Decl :: CDecl
i0Decl = CDecl "i0" (Just $ simpleExpr "I") []


i1Decl :: CDecl
i1Decl = CDecl "i1" (Just $ simpleExpr "I") []

negDecl :: CDecl
negDecl =
  let iI = CDecl "i"  (Just $ simpleExpr "I") []
      sI = simpleSpine "I"
      eq1 = CEquation (CSpine "~" [simpleExpr "i0"]) (simpleSpine "i1") True
      eq2 = CEquation (CSpine "~" [simpleExpr "i1"]) (simpleSpine "i0") True
  in
  CDecl {
    name = "~",
    typ = Just $ CExpr [iI] [] sI ,
    equations = [eq1, eq2]
  }

andDecl :: CDecl
andDecl =
  let eI = simpleExpr "I"
      iI = CDecl "i" (Just eI) []
      jI = CDecl "j" (Just eI) []
      sI = simpleSpine "I"
      eq1 = CEquation (CSpine "_∧_" [simpleExpr "i0", simpleExpr "j"]) (CSpine "i0" []) True
      eq2 = CEquation (CSpine "_∧_" [simpleExpr "i1", simpleExpr "j"]) (CSpine "j" []) True
      eq3 = CEquation (CSpine "_∧_" [simpleExpr "i", simpleExpr "i0"]) (CSpine "i0" []) True
      eq4 = CEquation (CSpine "_∧_" [simpleExpr "i", simpleExpr "i1"]) (CSpine "i" []) True
  in
  CDecl {
      name = "_∧_",
      typ = Just $ CExpr [iI, jI] [] sI,
      equations = [eq1, eq2, eq3, eq4]
    }


orDecl :: CDecl
orDecl =
  let eI = simpleExpr "I"
      iI = CDecl "i" (Just eI) []
      jI = CDecl "j" (Just eI) []
      sI = simpleSpine "I"
      eq1 = CEquation (CSpine "_∨_" [simpleExpr "i0", simpleExpr "j"]) (CSpine "j" []) True
      eq2 = CEquation (CSpine "_∨_" [simpleExpr "i1", simpleExpr "j"]) (CSpine "i1" []) True
      eq3 = CEquation (CSpine "_∨_" [simpleExpr "i", simpleExpr "i0"]) (CSpine "i" []) True
      eq4 = CEquation (CSpine "_∨_" [simpleExpr "i", simpleExpr "i1"]) (CSpine "i1" []) True
  in
  CDecl {
      name = "_∨_",
      typ = Just $ CExpr [iI, jI] [] sI,
      equations = [eq1, eq2, eq3, eq4]
    }
