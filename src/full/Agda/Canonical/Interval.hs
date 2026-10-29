-- | Normal form of the interval expressions in the answers of Canonical.
--
--   Canonical builds expressions of the interval with @primIMin@ (@_∧_@),
--   @primIMax@ (@_∨_@) and @primINeg@ (@~_@), and finds many variants of
--   the same one (@i ∨ i@, @(~ i ∨ i) ∧ ~ i@ for @i@, @~ i@).  Before they
--   are shown, they are put in disjunctive normal form: a disjunction of
--   conjunctions of literals (@i@ or @~ i@), without repetitions, without
--   a conjunction that contains another one (absorption), and sorted.
--
--   The interval is a De Morgan algebra, not a boolean one: @i ∧ ~ i@ is
--   not @i0@, so @i@ and @~ i@ are independent literals.  The normal form
--   only uses the laws of distributive lattices, De Morgan laws and the
--   involution of @~_@, which hold in Agda; Agda checks the solution anyway.

module Agda.Canonical.Interval (normaliseIntervals, faces) where

import Data.List (nub, nubBy, sortOn)

import Agda.Canonical.Types

-- | A literal: an atom, negated or not.
type Lit = (Bool, CSpine)

-- | A conjunction of literals; the empty one is @i1@.
type Conj = [Lit]

-- | A disjunction of conjunctions; the empty one is @i0@.
type DNF = [Conj]

-- | Puts the interval expressions of an answer in normal form, given the
--   names of @i0@ and @i1@.  Every maximal subterm built with @primIMin@,
--   @primIMax@ and @primINeg@ is normalised; its atoms (variables,
--   applications…) are normalised recursively.
normaliseIntervals :: (String, String) -> CExpr -> CExpr
normaliseIntervals ends@(i0, i1) = expr
  where
    expr (CExpr ps ls sp) = CExpr (map decl ps) (map decl ls) (spine sp)
    decl d = d { typ = expr <$> typ d }

    spine sp@(CSpine h as)
      | isOp sp   = fromDNF (toDNF ends spine False sp)
      | otherwise = CSpine h (map expr as)

    fromDNF :: DNF -> CSpine
    fromDNF []       = CSpine i0 []
    fromDNF [c]      = fromConj c
    fromDNF (c : cs) = op "primIMax" (fromConj c) (fromDNF cs)

    fromConj :: Conj -> CSpine
    fromConj []       = CSpine i1 []
    fromConj [l]      = lit l
    fromConj (l : ls) = op "primIMin" (lit l) (fromConj ls)

    lit (False, a) = a
    lit (True, a)  = CSpine "primINeg" [CExpr [] [] a]

    op f a b = CSpine f [CExpr [] [] a, CExpr [] [] b]

-- | The faces of an expression of the interval @φ@ (given the names of
--   @i0@ and @i1@), as in a system @λ { (i = i1) (j = i0) → … }@: the
--   conjunctions of its normal form, a literal @i@ being @i = i1@ and
--   @~ i@ being @i = i0@.  A conjunction with @i = i0@ and @i = i1@ is an
--   empty face, left out.  'Nothing' if an atom is not a variable, or if
--   @φ@ is @i1@, which a system cannot express.
faces :: (String, String) -> CSpine -> Maybe [[(String, Bool)]]
faces ends sp = case toDNF ends id False sp of
  d | any null d -> Nothing
    | otherwise  -> do
        cs <- mapM (mapM face) d
        return [ c | c <- map nub cs, and [ (x, not b) `notElem` c | (x, b) <- c ] ]
  where
    face (neg, CSpine x []) = Just (x, not neg)
    face _                  = Nothing

-- | An operator of the interval applied to expressions without binders.
isOp :: CSpine -> Bool
isOp (CSpine h as) = all plain as && case (h, length as) of
  ("primIMin", 2) -> True
  ("primIMax", 2) -> True
  ("primINeg", 1) -> True
  _               -> False
  where plain (CExpr ps ls _) = null ps && null ls

-- | The normal form of a spine, negated or not, given the names of @i0@ and
--   @i1@ and what to do with its atoms.
toDNF :: (String, String) -> (CSpine -> CSpine) -> Bool -> CSpine -> DNF
toDNF (i0, i1) atom = dnf
  where
    dnf neg sp@(CSpine h as)
      | isOp sp = case (h, map spineOf as) of
          ("primIMin", [a, b]) -> (if neg then disj else conj) (dnf neg a) (dnf neg b)
          ("primIMax", [a, b]) -> (if neg then conj else disj) (dnf neg a) (dnf neg b)
          (_, [a])             -> dnf (not neg) a
          _                    -> [[(neg, atom sp)]]
      | null as, h == i0 = if neg then top else bot
      | null as, h == i1 = if neg then bot else top
      | otherwise        = [[(neg, atom sp)]]
    spineOf (CExpr _ _ sp) = sp

    top = [[]]
    bot = []

    disj a b = absorb (a ++ b)
    conj a b = absorb [ nub (x ++ y) | x <- a, y <- b ]

-- | Removes the repeated conjunctions, and those that contain another one
--   (@x ∨ (x ∧ y) = x@), and sorts the literals and the conjunctions
--   (commutativity), so that equal expressions are printed the same way.
absorb :: DNF -> DNF
absorb cs = sortOn (map litKey) [ c | c <- cs', not (any (`strictlyIn` c) cs') ]
  where
    cs' = nubBy sameSet (map (sortOn litKey) cs)
    sameSet a b = all (`elem` b) a && all (`elem` a) b
    strictlyIn a b = all (`elem` b) a && not (sameSet a b)
    -- Atoms by their text, @i@ before @~ i@.
    litKey (neg, a) = (show a, neg)
