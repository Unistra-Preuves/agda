-- | Declarations that Canonical needs and that do not come from Agda
--   definitions.
--
--   * The universe @Type l@, which stands for @Set l@.
--
--   * Canonical has no universe-polymorphic dependent function type, so a
--     Π-type occurring as a term (e.g. as the argument of a datatype) is
--     encoded as the datatype
--
--     > Pi    : (u v : Level) (A : Type u) (B : A → Type v) → Type (u ⊔ v)
--     > Pi.mk : … (f : (a : A) → B a) → Pi u v A B          -- λ
--     > Pi.f  : … (p : Pi u v A B) (a : A) → B a            -- application
--     > Pi.f u v A B (Pi.mk _ _ _ _ g) a ⤇ g a              -- β
--
--   * The computation rules of @_⊔_@ on levels.

module Agda.Canonical.Builtin
  ( typeDecl, typeSig
  , piDecls, piSigs
  , levelMaxEqs
  ) where

import Agda.Canonical.Types
import Agda.Syntax.Common (Hiding(..))

-- | The universe @Type@, left untyped.
typeDecl :: CDecl
typeDecl = CDecl { name = "Type", typ = Nothing, equations = [] }

-- | Signature of 'typeDecl': one explicit level.
typeSig :: (String, Sig)
typeSig = ("Type", [Param 0 NotHidden])

-- | Declarations of @Pi@, @Pi.mk@ and @Pi.f@, which depend on @Level@ and @_⊔_@.
piDecls :: [CDecl]
piDecls =
  [ CDecl "Pi" (Just $ CExpr hdr [] (CSpine "Type" [lmax])) []
  , CDecl "Pi.mk"
      (Just $ CExpr (hdr ++ [typed "f" fnT]) [] (CSpine "Pi" piHd)) []
  , CDecl "Pi.f"
      (Just $ CExpr (hdr ++ [typed "p" piT, typed "a" (simpleExpr "A")]) []
                    (CSpine "B" [simpleExpr "a"]))
      -- The arguments of @Pi.mk@ are wildcards: Canonical does not apply
      -- a non-linear rule, and they are those of @Pi.f@ in a well-typed term.
      [ ruleVars ["u", "v", "A", "B", "u'", "v'", "A'", "B'", "g", "a", "y"] $ CEquation
          (CSpine "Pi.f" (lvls ++ [ simpleExpr "A", eta1 "B"
                                  , CExpr [] [] (CSpine "Pi.mk" [ simpleExpr "u'", simpleExpr "v'"
                                                                , simpleExpr "A'", eta1 "B'", eta1 "g" ])
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
    -- @λ y. n y@
    eta1 n = CExpr [CDecl "y" Nothing []] [] (CSpine n [simpleExpr "y"])
    -- @Type l@
    tyOf l = CExpr [] [] (CSpine "Type" [simpleExpr l])

-- | Signatures of 'piDecls', all parameters explicit.
piSigs :: [(String, Sig)]
piSigs = [("Pi", base), ("Pi.mk", base ++ [p 1]), ("Pi.f", base ++ [p 0, p 0])]
  where
    p n  = Param n NotHidden
    base = [p 0, p 0, p 0, p 1]

-- | Rewrite rules for @_⊔_@:
--
--   > lzero ⊔ x = x
--   > x ⊔ lzero = x
--   > lsuc x ⊔ lsuc y = lsuc (x ⊔ y)
--   > x ⊔ x = x
levelMaxEqs :: [CEquation]
levelMaxEqs = map (ruleVars ["x", "y"])
  [ CEquation (CSpine "_⊔_" [lz, x]) (CSpine "x" []) True
  , CEquation (CSpine "_⊔_" [x, lz]) (CSpine "x" []) True
  , CEquation (CSpine "_⊔_" [ls x, ls y])
              (CSpine "lsuc" [CExpr [] [] (CSpine "_⊔_" [x, y])]) True
  , CEquation (CSpine "_⊔_" [x, x]) (CSpine "x" []) True
  ]
  where
    x    = simpleExpr "x"
    y    = simpleExpr "y"
    lz   = CExpr [] [] (CSpine "lzero" [])
    ls e = CExpr [] [] (CSpine "lsuc" [e])
