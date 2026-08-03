module Agda.Canonical.Types where


import GHC.Generics (Generic)
import Data.Aeson
import Data.List (intercalate)
import Agda.Utils.Lens (set)
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Interaction.Base (Interaction'(Cmd_constraints))
import Agda.TypeChecking.Monad.Builtin (primIMin, primIMax, primINeg)
-- import Agda.Syntax.Common.Pretty

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
  let tS = CExpr [] [] (CSpine "Type" [simpleExpr "ℓ"])
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
  let tS = CExpr [] [] (CSpine "Type" [simpleExpr "ℓ"])
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
  let iI = CDecl "_"  (Just $ simpleExpr "I") []
      sI = simpleSpine "I"
      eq1 = CEquation (CSpine "primINeg" [simpleExpr "i0"]) (simpleSpine "i1") True
      eq2 = CEquation (CSpine "primINeg" [simpleExpr "i1"]) (simpleSpine "i0") True
      eq3 = CEquation (CSpine "primINeg" [CExpr [] [] (CSpine "primIMin" [simpleExpr "i", simpleExpr "j"])])
                      (CSpine "primIMax" [CExpr [] [] (CSpine "primINeg" [simpleExpr "i"]), CExpr [] [] (CSpine "primINeg" [simpleExpr "j"])]) True

      eq4 = CEquation (CSpine "primINeg" [CExpr [] [] (CSpine "primIMax" [simpleExpr "i", simpleExpr "j"])])
                      (CSpine "primIMin" [CExpr [] [] (CSpine "primINeg" [simpleExpr "i"]), CExpr [] [] (CSpine "primINeg" [simpleExpr "j"])]) True
  in
  CDecl {
    name = "primINeg",
    typ = Just $ CExpr [iI] [] sI ,
    equations = [eq1, eq2, eq3, eq4]
  }

andDecl :: CDecl
andDecl =
  let eI = simpleExpr "I"
      iI = CDecl "_" (Just eI) []
      jI = CDecl "_" (Just eI) []
      sI = simpleSpine "I"
      eq1 = CEquation (CSpine "primIMin" [simpleExpr "i0", simpleExpr "j"]) (CSpine "i0" []) True
      eq2 = CEquation (CSpine "primIMin" [simpleExpr "i1", simpleExpr "j"]) (CSpine "j" []) True
      eq3 = CEquation (CSpine "primIMin" [simpleExpr "i", simpleExpr "i0"]) (CSpine "i0" []) True
      eq4 = CEquation (CSpine "primIMin" [simpleExpr "i", simpleExpr "i1"]) (CSpine "i" []) True
  in
  CDecl {
      name = "primIMin",
      typ = Just $ CExpr [iI, jI] [] sI,
      equations = [eq1, eq2, eq3, eq4]
    }


orDecl :: CDecl
orDecl =
  let eI = simpleExpr "I"
      iI = CDecl "_" (Just eI) []
      jI = CDecl "_" (Just eI) []
      sI = simpleSpine "I"
      eq1 = CEquation (CSpine "primIMax" [simpleExpr "i0", simpleExpr "j"]) (CSpine "j" []) True
      eq2 = CEquation (CSpine "primIMax" [simpleExpr "i1", simpleExpr "j"]) (CSpine "i1" []) True
      eq3 = CEquation (CSpine "primIMax" [simpleExpr "i", simpleExpr "i0"]) (CSpine "i" []) True
      eq4 = CEquation (CSpine "primIMax" [simpleExpr "i", simpleExpr "i1"]) (CSpine "i1" []) True
      -- eq5 = CEquation (CSpine "primIMax" [simpleExpr "i", simpleExpr "j"]) (CSpine "primIMax" [simpleExpr "j", simpleExpr "i"]) False
  in
  CDecl {
      name = "primIMax",
      typ = Just $ CExpr [iI, jI] [] sI,
      equations = [eq1, eq2, eq3, eq4]
    }

cpittDecl :: CDecl
cpittDecl =
  let
      tL = simpleExpr "Level"
      tS = CExpr [] [] (CSpine "Type" [simpleExpr "ℓ"])
      typ' = CExpr [CDecl "ℓ" (Just $ tL) [],
                           CDecl "ℓ'" (Just $ tL) [],
                           CDecl "A" (Just $ tS) [],
                           CDecl "B" (Just $ (CExpr [CDecl "_" (Just $ simpleExpr "A") []] [] (CSpine "Type" [simpleExpr "ℓ'"]))) []]
                           []
                           (CSpine "Type" [CExpr [] [] (CSpine "_⊔_" [simpleExpr "ℓ", simpleExpr "ℓ'"])])
  in
  CDecl {
    name = "Canonical.PiTypeType",
    typ = Just $ typ',
    equations = []
  }

-- cpitsDecl :: CDecl
-- cpitsDecl =
--   let
--       tL = simpleExpr "Level"
--       tS = CExpr [] [] (CSpine "Type" [simpleExpr "ℓ"])
--       typ' = CExpr [CDecl "ℓ" (Just $ tL) [],
--                            CDecl "ℓ'" (Just $ tL) [],
--                            CDecl "A" (Just $ tS) [],
--                            CDecl "B" (Just $ (CExpr [CDecl "_" (Just $ simpleExpr "A") []] [] (CSpine "ß" [simpleExpr "ℓ'"]))) []]
--                            []
--                            (CSpine "ß" [CExpr [] [] (CSpine "_⊔_" [simpleExpr "ℓ", simpleExpr "ℓ'"])])
--   in
--   CDecl {
--     name = "Canonical.PiTypeß",
--     typ = Just $ typ',
--     equations = []
--   }

cpistDecl :: CDecl
cpistDecl =
  let
      tL = simpleExpr "Level"
      tS = CExpr [] [] (CSpine "ß" [simpleExpr "ℓ"])
      typ' = CExpr [CDecl "ℓ" (Just $ tL) [],
                           CDecl "ℓ'" (Just $ tL) [],
                           CDecl "A" (Just $ tS) [],
                           CDecl "B" (Just $ (CExpr [CDecl "_" (Just $ simpleExpr "A") []] [] (CSpine "Type" [simpleExpr "ℓ'"]))) []]
                           []
                           (CSpine "ß" [CExpr [] [] (CSpine "_⊔_" [simpleExpr "ℓ", simpleExpr "ℓ'"])])
  in
  CDecl {
    name = "Canonical.PißType",
    typ = Just $ typ',
    equations = []
  }


cpistmkDecl :: CDecl
cpistmkDecl =
  let
      tL = simpleExpr "Level"
      tS = CExpr [] [] (CSpine "ß" [simpleExpr "ℓ"])
      typ' = CExpr [CDecl "ℓ" (Just $ tL) [],
                           CDecl "ℓ'" (Just $ tL) [],
                           CDecl "A" (Just $ tS) [],
                           CDecl "B" (Just $ (CExpr [CDecl "_" (Just $ simpleExpr "A") []] [] (CSpine "Type" [simpleExpr "ℓ'"]))) [],
                           CDecl "f" (Just $ (CExpr [CDecl "a" (Just $ simpleExpr "A") []] [] (CSpine "B" [simpleExpr "a"]))) []]
                           []
                           (CSpine "Canonical.PißType" [simpleExpr "ℓ",
                                                         simpleExpr "ℓ'",
                                                         simpleExpr "A",
                                                         CExpr [CDecl "a" Nothing []]
                                                               []
                                                               (CSpine "B" [simpleExpr "a"])])

  in
  CDecl {
    name = "Canonical.PißType.mk",
    typ = Just $ typ',
    equations = []
  }


cpistfDecl :: CDecl
cpistfDecl =
  let
      tL = simpleExpr "Level"
      tS = CExpr [] [] (CSpine "ß" [simpleExpr "ℓ"])
      typ' = CExpr [CDecl "ℓ" (Just $ tL) [],
                           CDecl "ℓ'" (Just $ tL) [],
                           CDecl "A" (Just $ tS) [],
                           CDecl "B" (Just $ (CExpr [CDecl "_" (Just $ simpleExpr "A") []] [] (CSpine "Type" [simpleExpr "ℓ'"]))) [],
                           CDecl "self" (Just $ (CExpr [] [] (CSpine "Canonical.PißType" [simpleExpr "ℓ",
                                                                                     simpleExpr "ℓ'",
                                                                                     simpleExpr "A",
                                                                                     CExpr [CDecl "a" Nothing []]
                                                                                           []
                                                                                           (CSpine "B" [simpleExpr "a"])]))) [],
                           CDecl "a" (Just $ simpleExpr "A") []]
                           []
                           (CSpine "B" [simpleExpr "a"])
      lhs = CSpine "Canonical.PißType.f" [simpleExpr "ℓ",
                                               simpleExpr "ℓ'",
                                               simpleExpr "A",
                                               simpleExpr "B",
                                               CExpr [] [] (CSpine "Canonical.PißType.mk" [simpleExpr "ℓ",
                                                                                      simpleExpr "ℓ'",
                                                                                      simpleExpr "A",
                                                                                      simpleExpr "B",
                                                                                      simpleExpr "f"]),
                                               simpleExpr "a"]
      rhs = CSpine "f" [simpleExpr "a"]

  in
  CDecl {
    name = "Canonical.PißType.f",
    typ = Just $ typ',
    equations = [CEquation lhs rhs True]
  }

-- cpissDecl :: CDecl
-- cpissDecl =
--   let
--       tL = simpleExpr "Level"
--       tS = CExpr [] [] (CSpine "ß" [simpleExpr "ℓ"])
--       typ' = CExpr [CDecl "ℓ" (Just $ tL) [],
--                            CDecl "ℓ'" (Just $ tL) [],
--                            CDecl "A" (Just $ tS) [],
--                            CDecl "B" (Just $ (CExpr [CDecl "_" (Just $ simpleExpr "A") []] [] (CSpine "ß" [simpleExpr "ℓ'"]))) []]
--                            []
--                            (CSpine "ß" [CExpr [] [] (CSpine "_⊔_" [simpleExpr "ℓ", simpleExpr "ℓ'"])])
--   in
--   CDecl {
--     name = "Canonical.Pißß",
--     typ = Just $ typ',
--     equations = []
--   }

cpittmkDecl :: CDecl
cpittmkDecl =
  let
      tL = simpleExpr "Level"
      tS = CExpr [] [] (CSpine "Type" [simpleExpr "ℓ"])
      typ' = CExpr [CDecl "ℓ" (Just $ tL) [],
                           CDecl "ℓ'" (Just $ tL) [],
                           CDecl "A" (Just $ tS) [],
                           CDecl "B" (Just $ (CExpr [CDecl "_" (Just $ simpleExpr "A") []] [] (CSpine "Type" [simpleExpr "ℓ'"]))) [],
                           CDecl "f" (Just $ (CExpr [CDecl "a" (Just $ simpleExpr "A") []] [] (CSpine "B" [simpleExpr "a"]))) []]
                           []
                           (CSpine "Canonical.PiTypeType" [simpleExpr "ℓ",
                                                         simpleExpr "ℓ'",
                                                         simpleExpr "A",
                                                         CExpr [CDecl "a" Nothing []]
                                                               []
                                                               (CSpine "B" [simpleExpr "a"])])

  in
  CDecl {
    name = "Canonical.PiTypeType.mk",
    typ = Just $ typ',
    equations = []
  }


cpittfDecl :: CDecl
cpittfDecl =
  let
      tL = simpleExpr "Level"
      tS = CExpr [] [] (CSpine "Type" [simpleExpr "ℓ"])
      typ' = CExpr [CDecl "ℓ" (Just $ tL) [],
                           CDecl "ℓ'" (Just $ tL) [],
                           CDecl "A" (Just $ tS) [],
                           CDecl "B" (Just $ (CExpr [CDecl "_" (Just $ simpleExpr "A") []] [] (CSpine "Type" [simpleExpr "ℓ'"]))) [],
                           CDecl "self" (Just $ (CExpr [] [] (CSpine "Canonical.PiTypeType" [simpleExpr "ℓ",
                                                                                     simpleExpr "ℓ'",
                                                                                     simpleExpr "A",
                                                                                     CExpr [CDecl "a" Nothing []]
                                                                                           []
                                                                                           (CSpine "B" [simpleExpr "a"])]))) [],
                           CDecl "a" (Just $ simpleExpr "A") []]
                           []
                           (CSpine "B" [simpleExpr "a"])
      lhs = CSpine "Canonical.PiTypeType.f" [simpleExpr "ℓ",
                                               simpleExpr "ℓ'",
                                               simpleExpr "A",
                                               simpleExpr "B",
                                               CExpr [] [] (CSpine "Canonical.PiTypeType.mk" [simpleExpr "ℓ",
                                                                                      simpleExpr "ℓ'",
                                                                                      simpleExpr "A",
                                                                                      simpleExpr "B",
                                                                                      simpleExpr "f"]),
                                               simpleExpr "a"]
      rhs = CSpine "f" [simpleExpr "a"]

  in
  CDecl {
    name = "Canonical.PiTypeType.f",
    typ = Just $ typ',
    equations = [CEquation lhs rhs True]
  }

primHCompEquations :: [CEquation]
primHCompEquations =
  let lhs1 = CSpine "primHComp" [simpleExpr "ℓ",
                                 simpleExpr "A",
                                 simpleExpr "i1",
                                 simpleExpr "u",
                                 simpleExpr "u0"]
      rhs1 = CSpine "u" [simpleExpr "i1", simpleExpr "itIsOne"]
  --     rhs1 = CSpine "Canonical.PißType.f" [simpleExpr "lzero", simpleExpr "ℓ", (CExpr [] [] (CSpine "IsOne" [simpleExpr "i1"])),
  --                                                    CExpr [CDecl "_" Nothing
  --                                                                 -- (Just $ CExpr [] [] (CSpine "IsOne" [simpleExpr "i1"]))
  --                                                                 []]
  --                                                          [] (CSpine "A" [{-simpleExpr "o"-}]),
  --                                                    CExpr [] [] (CSpine "u" [simpleExpr "i1"]),
  --                                                   -- CExpr [] [] (CSpine "Canonical.PißType.mk" [simpleExpr "lzero", simpleExpr "ℓ", (CExpr [] [] (CSpine "IsOne" [simpleExpr "i1"])), CExpr [CDecl "_" Nothing []] [] (CSpine "A" []), CExpr [] [] (CSpine "u" [simpleExpr "i1"])]),
  --                        simpleExpr "itIsOne"]
  in
  [CEquation lhs1 rhs1 True]

primLevelMaxEquations :: [CEquation]
primLevelMaxEquations =
  let lhs1 = CSpine "_⊔_" [simpleExpr "ℓ", simpleExpr "lzero"]
      rhs1 = CSpine "ℓ" []
      lhs2 = CSpine "_⊔_" [simpleExpr "lzero", simpleExpr "ℓ"]
      rhs2 = CSpine "ℓ" []
  in
  [CEquation lhs1 rhs1 True, CEquation lhs2 rhs2 True]

partialEquations :: [CEquation]
partialEquations =
   let lhs = CSpine "Partial" [simpleExpr "ℓ", simpleExpr "φ", simpleExpr "A"]
       rhs = CSpine "PartialP" [simpleExpr "ℓ", simpleExpr "φ", CExpr [CDecl "_" Nothing []] [] (simpleSpine "A")]
   in
   [CEquation lhs rhs True]


partialPEquations :: [CEquation]
partialPEquations =
   let lhs = CSpine "PartialP" [simpleExpr "ℓ", simpleExpr "φ", simpleExpr "A"]
       rhs = CSpine "Canonical.PißType" [simpleExpr "lzero", simpleExpr "ℓ", CExpr [] [] (CSpine "IsOne" [simpleExpr "φ"]),
                                                   CExpr [CDecl "o" (Just $ CExpr [] [] (CSpine "IsOne" [simpleExpr "φ"]) ) []] [] (CSpine "A" [simpleExpr "o"])]
   in
   [CEquation lhs rhs True]

eqEquations :: [CEquation]
eqEquations =
  let lhs = CSpine "_≡_" [simpleExpr "ℓ", simpleExpr "A", simpleExpr "x", simpleExpr "y"]
      rhs = CSpine "PathP" [simpleExpr "ℓ", CExpr [CDecl "_" (Just $ simpleExpr "I") []] [] (CSpine "A" []), simpleExpr "x", simpleExpr "y"]
  in
  [CEquation lhs rhs True]

primPOrEquations :: [CEquation]
primPOrEquations =
  let lhs1 = CSpine "primPOr" [simpleExpr "ℓ", simpleExpr "i0", simpleExpr "j", simpleExpr "A", simpleExpr "u", simpleExpr "v", simpleExpr "o"]
      rhs1 = CSpine "v" [simpleExpr "o"]
      lhs2 = CSpine "primPOr" [simpleExpr "ℓ", simpleExpr "i1", simpleExpr "j", simpleExpr "A", simpleExpr "u", simpleExpr "v", simpleExpr "o"]
      rhs2 = CSpine "u" [simpleExpr "itIsOne"]
      lhs3 = CSpine "primPOr" [simpleExpr "ℓ", simpleExpr "i", simpleExpr "i0", simpleExpr "A", simpleExpr "u", simpleExpr "v", simpleExpr "o"]
      rhs3 = CSpine "u" [simpleExpr "o"]
      lhs4 = CSpine "primPOr" [simpleExpr "ℓ", simpleExpr "i", simpleExpr "i1", simpleExpr "A", simpleExpr "u", simpleExpr "v", simpleExpr "o"]
      rhs4 = CSpine "v" [simpleExpr "itIsOne"]
  in
  [CEquation lhs1 rhs1 True,
   CEquation lhs2 rhs2 True,
   CEquation lhs3 rhs3 True,
   CEquation lhs4 rhs4 True]


primPOrDecl :: CDecl
primPOrDecl =
  let ld = CDecl "ℓ" (Just $ simpleExpr "Level") []
      id = CDecl "i" (Just $ simpleExpr "I") []
      jd = CDecl "j" (Just $ simpleExpr "I") []
      -- ad = CDecl "A" (Just $ CExpr [] [] (CSpine "Partial" [CExpr [] [] (CSpine "lsuc" [simpleExpr "ℓ"]), ioj, CExpr [] [] (CSpine "Type" [simpleExpr "ℓ"])])) []
      ad = CDecl "A" (Just $ CExpr [(CDecl "_" (Just $ CExpr [] [] (CSpine "IsOne" [ioj])) [])] [] (CSpine "Type" [simpleExpr "ℓ"]) ) []
      us2as = CSpine "A" [CExpr [] [] (CSpine "IsOne1" [simpleExpr "i", simpleExpr "j", simpleExpr "o"])]
      -- us2as = CSpine "Canonical.PißType.f" [simpleExpr "lzero",
      --                                                 CExpr [] [] (CSpine "lsuc" [simpleExpr "ℓ"]),
      --                                                 CExpr [] [] (CSpine "IsOne" [ioj]),
      --                                                 CExpr [(CDecl "o" Nothing [])] [] (CSpine "Type" [simpleExpr "ℓ"]),
      --                                                 simpleExpr "A",
      --                                                 -- CExpr [] [] (CSpine "Canonical.PißType.mk" [simpleExpr "lzero",
      --                                                 --                                             CExpr [] [] (CSpine "lsuc" [simpleExpr "ℓ"]),
      --                                                 --                                             CExpr [] [] (CSpine "IsOne" [ioj]),
      --                                                 --                                             CExpr [(CDecl "o" Nothing [])] [] (CSpine "Type" [simpleExpr "ℓ"]), simpleExpr "A"]),
      --                                                 CExpr [] [] (CSpine "IsOne1" [simpleExpr "i", simpleExpr "j", simpleExpr "z"])]
      us2a = CExpr [] [] us2as
      -- us2a = CExpr [CDecl "z" Nothing []] [] us2as
      -- ud = CDecl "u" (Just $ CExpr [] [] (CSpine "PartialP" [simpleExpr "ℓ", simpleExpr "i", us2a])) []
      ud = CDecl "u" (Just $ CExpr [CDecl "o" (Just $ CExpr [] [] (CSpine "IsOne" [simpleExpr "i"])) []] [] (us2as)) []
      vs2as = CSpine "A" [CExpr [] [] (CSpine "IsOne2" [simpleExpr "i", simpleExpr "j", simpleExpr "o"])]
      -- vs2as = CSpine "Canonical.PißType.f" [simpleExpr "lzero",
      --                                                 CExpr [] [] (CSpine "lsuc" [simpleExpr "ℓ"]),
      --                                                 CExpr [] [] (CSpine "IsOne" [ioj]),
      --                                                 CExpr [(CDecl "o" Nothing [])] [] (CSpine "Type" [simpleExpr "ℓ"]),
      --                                                 simpleExpr "A",
      --                                                 -- CExpr [] [] (CSpine "Canonical.PißType.mk" [simpleExpr "lzero",
      --                                                 --                                             CExpr [] [] (CSpine "lsuc" [simpleExpr "ℓ"]),
      --                                                 --                                             CExpr [] [] (CSpine "IsOne" [ioj]),
      --                                                 --                                             CExpr [(CDecl "o" Nothing [])] [] (CSpine "Type" [simpleExpr "ℓ"]), simpleExpr "A"]),
      --                                                 CExpr [] [] (CSpine "IsOne2" [simpleExpr "i", simpleExpr "j", simpleExpr "z"])]
      vs2a = CExpr [] [] vs2as
      -- vs2a = CExpr [CDecl "z" Nothing []] [] vs2as
      -- vd = CDecl "v" (Just $ CExpr [] [] (CSpine "PartialP" [simpleExpr "ℓ",simpleExpr "j", vs2a])) []
      vd = CDecl "v" (Just $ CExpr [CDecl "o" (Just $ CExpr [] [] (CSpine "IsOne" [simpleExpr "j"])) []] [] (vs2as)) []
      od = CDecl "o" (Just $ CExpr [] [] (CSpine "IsOne" [ioj])) []
      ioj = CExpr [] [] (CSpine "primIMax" [simpleExpr "i", simpleExpr "j"])
      typ' = CExpr [ld, id, jd, ad, ud, vd, od] [] (CSpine "A" [simpleExpr "o"])
  in
  CDecl {
    name = "primPOr",
    typ = Just typ',
    equations = primPOrEquations
  }

primHCompDecl :: CDecl
primHCompDecl =
  let ld = CDecl "ℓ" (Just $ simpleExpr "Level") []
      ad = CDecl "A" (Just $ CExpr [] [] (CSpine "Type" [simpleExpr "ℓ"])) []
      id = CDecl "φ" (Just $ simpleExpr "I") []
      ud = CDecl "u" (Just $ CExpr [(CDecl "i" (Just $ simpleExpr "I") []), CDecl "o" (Just $ CExpr [] [] (CSpine "IsOne" [simpleExpr "φ"])) []] [] (CSpine "A" [])) []
      aad = CDecl "u0" (Just $ CExpr [] [] (CSpine "Sub" [simpleExpr "ℓ", simpleExpr "A", simpleExpr "φ", CExpr [CDecl "o" Nothing []] [] (CSpine "u" [simpleExpr "i0", simpleExpr "o"])])) []
      -- aad = CDecl "a" (Just $ simpleExpr "A") [CEquation (simpleSpine "a") (CSpine "u" [simpleExpr "i0", simpleExpr "itIsOne"]) False]
  in
  CDecl "primHComp" (Just $ (CExpr [ld, ad, id, ud, aad] [] (simpleSpine "A"))) primHCompEquations


inSDecl :: CDecl
inSDecl =
  let ld = CDecl "ℓ" (Just $ simpleExpr "Level") []
      ad = CDecl "A" (Just $ CExpr [] [] (CSpine "Type" [simpleExpr "ℓ"])) []
      id = CDecl "φ" (Just $ simpleExpr "I") []
      aad = CDecl "a" (Just $ simpleExpr "A") []
      -- lhs = CSpine "inS" [simpleExpr "ℓ'", simpleExpr "A'", simpleExpr "φ'", CExpr [] [] (CSpine "outS" [simpleExpr "ℓ", simpleExpr "A", simpleExpr "i", simpleExpr "u", simpleExpr "a"])]
      -- rhs = CSpine "" []
  in
  CDecl "inS" (Just $ (CExpr [ld, ad, id, aad] [] (CSpine "Sub" [simpleExpr "ℓ", simpleExpr "A", simpleExpr "φ", (CExpr [CDecl "_" Nothing []] [] (simpleSpine "a" ))]))) []

subDecl :: CDecl
subDecl =
  let ld = CDecl "ℓ" (Just $ simpleExpr "Level") []
      ad = CDecl "A" (Just $ CExpr [] [] (CSpine "Type" [simpleExpr "ℓ"])) []
      id = CDecl "φ" (Just $ simpleExpr "I") []
      od = CDecl "_" (Just $ (CExpr [(CDecl "_" (Just $ CExpr [] [] (CSpine "IsOne" [simpleExpr "φ"])) [])] [] (simpleSpine "A"))) []
  in
  CDecl "Sub" (Just $ CExpr [ld, ad, id, od] [] (CSpine "ß" [simpleExpr "ℓ"])) []

outSEquations :: [CEquation]
outSEquations =
  let lhs1 = CSpine "outS" [simpleExpr "ℓ", simpleExpr "A", simpleExpr "i1", simpleExpr "u", simpleExpr "_"]
      rhs1 = CSpine "u" [simpleExpr "itIsOne"]
      lhs2 = CSpine "outS" [simpleExpr "ℓ", simpleExpr "A", simpleExpr "i", simpleExpr "u", CExpr [] [] (CSpine "inS" [simpleExpr "ℓ", simpleExpr "A", simpleExpr "i", simpleExpr "a"])]
      rhs2 = CSpine "a" []
  in
  [CEquation lhs1 rhs1 True, CEquation lhs2 rhs2 False]

outSDecl :: CDecl
outSDecl =
  let ld = CDecl "ℓ" (Just $ simpleExpr "Level") []
      ad = CDecl "A" (Just $ CExpr [] [] (CSpine "Type" [simpleExpr "ℓ"])) []
      id = CDecl "φ" (Just $ simpleExpr "I") []
      od = CDecl "u" (Just $ (CExpr [(CDecl "_" (Just $ CExpr [] [] (CSpine "IsOne" [simpleExpr "φ"])) [])] [] (simpleSpine "A"))) []
      sd = CDecl "_" (Just $ (CExpr [] [] (CSpine "Sub" [simpleExpr "ℓ", simpleExpr "A", simpleExpr "φ", simpleExpr "u"]))) []
  in
  CDecl "outS" (Just $ (CExpr [ld, ad, id, od, sd] [] (simpleSpine "A")) ) outSEquations




-- testGoal :: CDecl
-- testGoal =
--   let ad = CDecl "A" (Just $ CExpr [] [] (CSpine "Type" [])) []
--       id = CDecl "i" (Just $ CExpr [] [] (simpleSpine "I")) []
--       jd = CDecl "j" (Just $ CExpr [] [] (simpleSpine "I")) []
--       xd = CDecl "x" (Just $ simpleExpr "A") []
--       yd = CDecl "y" (Just $ simpleExpr "A") []
--       plhs0 = CSpine "p" [simpleExpr "i0"]
--       prhs0 = CSpine "x" []
--       plhs1 = CSpine "p" [simpleExpr "i1"]
--       prhs1 = CSpine "y" []
--       pd = CDecl "p" (Just $ CExpr [CDecl "k" (Just $ simpleExpr "I") []] [] (simpleSpine "A")) [CEquation plhs0 prhs0 True, CEquation plhs1 prhs1 True]
--
--       glhs0 = CSpine "Goal" [simpleExpr "i0", simpleExpr "j"]
--       grhs0 = CSpine "x" []
--       glhs1 = CSpine "Goal" [simpleExpr "i1", simpleExpr "j"]
--       grhs1 = CSpine "p" [simpleExpr "j"]
--       glhs2 = CSpine "Goal" [simpleExpr "i", simpleExpr "i0"]
--       grhs2 = CSpine "x" []
--       glhs3 = CSpine "Goal" [simpleExpr "i", simpleExpr "i1"]
--       grhs3 = CSpine "p" [simpleExpr "i"]
--   in
--   CDecl {
--       name = "Goal",
--       typ = Just $ (CExpr [id, jd] [typeDecl, iDecl, i0Decl, i1Decl, negDecl, orDecl, andDecl, ad, xd, yd, pd] (simpleSpine "A")),
--       equations = [
--         CEquation glhs0 grhs0 True,
--         CEquation glhs1 grhs1 True,
--         CEquation glhs2 grhs2 True,
--         CEquation glhs3 grhs3 True
--       ]
--     }
--

-- testGoal :: CDecl
-- testGoal =
--   let ad = CDecl "A" (Just $ CExpr [] [] (CSpine "Type" [])) []
--       id = CDecl "i" (Just $ CExpr [] [] (simpleSpine "I")) []
--       jd = CDecl "j" (Just $ CExpr [] [] (simpleSpine "I")) []
--       kd = CDecl "k" (Just $ CExpr [] [] (simpleSpine "I")) []
--       xd = CDecl "x" (Just $ simpleExpr "A") []
--       yd = CDecl "y" (Just $ simpleExpr "A") []
--       plhs0 = CSpine "p" [simpleExpr "i0"]
--       prhs0 = CSpine "x" []
--       plhs1 = CSpine "p" [simpleExpr "i1"]
--       prhs1 = CSpine "y" []
--       pd = CDecl "p" (Just $ CExpr [CDecl "l" (Just $ simpleExpr "I") []] [] (simpleSpine "A")) [CEquation plhs0 prhs0 True, CEquation plhs1 prhs1 True]
--
--       glhs0 = CSpine "Goal" [simpleExpr "i0", simpleExpr "j", simpleExpr "k"]
--       grhs0 = CSpine "p" [simpleExpr "k"]
--       glhs1 = CSpine "Goal" [simpleExpr "i1", simpleExpr "j", simpleExpr "k"]
--       grhs1 = CSpine "p" [CExpr [] [] (CSpine "primIMax" [simpleExpr "j", simpleExpr "k"])]
--       glhs2 = CSpine "Goal" [simpleExpr "i", simpleExpr "i0", simpleExpr "k"]
--       grhs2 = CSpine "p" [simpleExpr "k"]
--       glhs3 = CSpine "Goal" [simpleExpr "i", simpleExpr "i1", simpleExpr "k"]
--       grhs3 = CSpine "p" [CExpr [] [] (CSpine "primIMax" [simpleExpr "i", simpleExpr "k"])]
--       glhs4 = CSpine "Goal" [simpleExpr "i", simpleExpr "j", simpleExpr "i0"]
--       grhs4 = CSpine "p" [CExpr [] [] (CSpine "primIMin" [simpleExpr "i", simpleExpr "j"])]
--       glhs5 = CSpine "Goal" [simpleExpr "i", simpleExpr "j", simpleExpr "i1"]
--       grhs5 = CSpine "y" []
--   in
--   CDecl {
--       name = "Goal",
--       typ = Just $ (CExpr [id, jd, kd] [typeDecl, iDecl, i0Decl, i1Decl, negDecl, orDecl, andDecl, ad, xd, yd, pd] (simpleSpine "A")),
--       equations = [
--         CEquation glhs0 grhs0 True,
--         CEquation glhs1 grhs1 True,
--         CEquation glhs2 grhs2 True,
--         CEquation glhs3 grhs3 True,
--         CEquation glhs4 grhs4 True,
--         CEquation glhs5 grhs5 True
--       ]
--     }

testGoal :: CDecl
testGoal =
  let -- ad = CDecl "A" (Just $ CExpr [] [] (CSpine "Type" [])) []
      id = CDecl "i'" (Just $ CExpr [] [] (simpleSpine "I")) []
      jd = CDecl "j'" (Just $ CExpr [] [] (simpleSpine "I")) []
      kd = CDecl "k'" (Just $ CExpr [] [] (simpleSpine "I")) []
      -- xd = CDecl "x" (Just $ simpleExpr "A") []
      -- yd = CDecl "y" (Just $ simpleExpr "A") []
      -- plhs0 = CSpine "p" [simpleExpr "i0"]
      -- prhs0 = CSpine "x" []
      -- plhs1 = CSpine "p" [simpleExpr "i1"]
      -- prhs1 = CSpine "y" []
      -- pd = CDecl "p" (Just $ CExpr [CDecl "l" (Just $ simpleExpr "I") []] [] (simpleSpine "A")) [CEquation plhs0 prhs0 True, CEquation plhs1 prhs1 True]

      glhs0 = CSpine "Goal" [simpleExpr "i0", simpleExpr "j'", simpleExpr "k'"]
      grhs0 = CSpine "k'" []
      glhs1 = CSpine "Goal" [simpleExpr "i1", simpleExpr "j'", simpleExpr "k'"]
      grhs1 = CSpine "primIMax" [simpleExpr "j'", simpleExpr "k'"]
      glhs2 = CSpine "Goal" [simpleExpr "i'", simpleExpr "i0", simpleExpr "k'"]
      grhs2 = CSpine "k'" []
      glhs3 = CSpine "Goal" [simpleExpr "i'", simpleExpr "i1", simpleExpr "k'"]
      grhs3 = CSpine "primIMax" [simpleExpr "i'", simpleExpr "k'"]
      glhs4 = CSpine "Goal" [simpleExpr "i'", simpleExpr "j'", simpleExpr "i0"]
      grhs4 = CSpine "primIMin" [simpleExpr "i'", simpleExpr "j'"]
      glhs5 = CSpine "Goal" [simpleExpr "i'", simpleExpr "j'", simpleExpr "i1"]
      grhs5 = CSpine "i1" []
  in
  CDecl {
      name = "Goal",
      typ = Just $ (CExpr [id, jd, kd] [typeDecl, iDecl, i0Decl, i1Decl, negDecl, orDecl, andDecl] (simpleSpine "I")),
      equations = [
        CEquation glhs0 grhs0 True,
        CEquation glhs1 grhs1 True,
        CEquation glhs2 grhs2 True,
        CEquation glhs3 grhs3 True,
        CEquation glhs4 grhs4 True,
        CEquation glhs5 grhs5 True
      ]
    }
