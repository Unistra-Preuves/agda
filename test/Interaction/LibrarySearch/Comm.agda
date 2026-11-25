module LibrarySearch.Comm where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import LibrarySearch.Lib

+-suc : (m n : Nat) → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-comm : (m n : Nat) → m + n ≡ n + m
+-comm zero    n = sym (+-zero n)
+-comm (suc m) n = trans (cong suc (+-comm m n)) (sym (+-suc n m))
