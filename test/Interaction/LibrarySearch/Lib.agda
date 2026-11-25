module LibrarySearch.Lib where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

+-zero : (n : Nat) → n + zero ≡ n
+-zero zero    = refl
+-zero (suc n) = cong suc (+-zero n)

data _≤_ : Nat → Nat → Set where
  z≤n : {n : Nat} → zero ≤ n
  s≤s : {m n : Nat} → m ≤ n → suc m ≤ suc n

≤-trans : {a b c : Nat} → a ≤ b → b ≤ c → a ≤ c
≤-trans z≤n     _       = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

private
  postulate hidden : (n : Nat) → n * zero ≡ zero
