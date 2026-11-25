-- Library search: exact? and apply?

module LibrarySearch where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import LibrarySearch.Lib using (_≤_; ≤-trans; +-zero)
-- LibrarySearch.Comm.+-comm is only reachable through LibrarySearch.Mid.
import LibrarySearch.Mid

-- Solved by a lemma in scope, whose explicit arguments are hypotheses.
t0 : (a b c : Nat) → a ≤ b → b ≤ c → a ≤ c
t0 a b c p q = {!!}

-- Needs first-order matching: ?m + zero = a + zero is postponed by
-- the unifier.
t1 : (a : Nat) → a + zero ≡ a
t1 a = {!!}

-- Solved by the local context alone.
t2 : (a b : Nat) → a ≤ b → a ≤ b
t2 a b p = {!!}

-- Solved by a constructor.
t3 : (n : Nat) → suc n ≡ suc n
t3 n = {!!}

-- The lemma is not in scope: it is shown, but not inserted.
t4 : (a b : Nat) → a + b ≡ b + a
t4 a b = {!!}

-- The only lemma is private: nothing is found.
t5 : (a : Nat) → a * zero ≡ zero
t5 a = {!!}

-- apply? leaves subgoals.
t6 : (a c : Nat) → a ≤ c
t6 a c = {!!}

-- A lemma of a parameterised module.
module P (k : Nat) where
  postulate lemP : (n : Nat) → n * k ≡ k * n

  t7 : (n : Nat) → n * k ≡ k * n
  t7 n = {!!}

-- A field re-exported in a record (open ... public), as RingStr does
-- with IsRing: a projection-like function, applied without the record
-- parameters in the internal syntax (used to raise __IMPOSSIBLE__).
record IsComm (_·_ : Nat → Nat → Nat) : Set where
  field ·-comm : (a b : Nat) → a · b ≡ b · a

record CommStr : Set where
  field
    _⋆_    : Nat → Nat → Nat
    isComm : IsComm _⋆_
  open IsComm isComm public

t8 : (S : CommStr) (a b : Nat) → CommStr._⋆_ S a b ≡ CommStr._⋆_ S b a
t8 S a b = {!!}
