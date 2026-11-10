-- Test file for nested projections in Canonical

open import Data.Product
open import Data.Nat

-- Test 1: Simple nested projection
test1 : ∀ (p : Σ (Nat × Nat)) → Nat
test1 p = {! +debug !}

-- Test 2: Nested projection with more complex type
test2 : ∀ (p : Σ (Σ Nat (λ _ → Nat))) → Nat
test2 p = {! +debug !}

-- Test 3: Multiple nested projections
test3 : ∀ (p : Σ (Nat × Nat × Nat)) → Nat
test3 p = {! +debug !}

-- Test 4: Projection in a let binding
test4 : ∀ (p : Σ (Nat × Nat)) → Nat
test4 p = let x = p .fst .fst in {! +debug !}
