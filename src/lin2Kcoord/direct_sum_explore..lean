import algebra.module.basic
import linear_algebra.affine_space.affine_equiv
import algebra.direct_sum.basic
import algebra.direct_sum.module
-- import algebra.direct_sum
-- import linear_algebra.direct_sum_module
import tactic.linarith

/-
The type, fin n, of all natural numbers < n
-/

-- equivalent expressions
#check (⟨ 0, by linarith ⟩ : fin 2) -- checks
#check (⟨ 1, by linarith ⟩ : fin 2) -- checks
#check (⟨ 2, by linarith ⟩ : fin 2) -- nocheck
#reduce (⟨ 0, by linarith ⟩ : fin 2) -- checks
#reduce (⟨ 1, by linarith ⟩ : fin 2) -- checks

-- notation
#check (0 : fin 2)
-- provably equal to expanded term
example : (0 : fin 2) = (⟨ 0, by linarith ⟩) := rfl

#check (0 : fin 2) -- 0
#check (1 : fin 2) -- 1
#check (2 : fin 2) -- not a type error

#eval (0 : fin 2) -- 0
#eval (1 : fin 2) -- 1
#eval (2 : fin 2) -- 0, modulus conversion

/-
The type, fin n → Type 
-/

def indexed_family : (fin 2) → Type 
| ⟨ 0, _ ⟩  := ℚ
| ⟨ 1, _ ⟩  := ℕ 
| ⟨ _, p ⟩ := empty -- can't happen

#reduce indexed_family 0  -- ℚ  
#reduce indexed_family 1  -- ℕ 
#reduce indexed_family 2  -- ℚ, not empty (coercion again)




/-
The type, finset α

It's defined as a structure with 2 fields:
  - val is a multiset α of elements;
  - nodup is a proof that val has no duplicates.
-/

