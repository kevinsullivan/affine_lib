import algebra.module.basic
import linear_algebra.affine_space.affine_equiv
import algebra.direct_sum.basic
import algebra.direct_sum.module
import tactic.linarith
import .lin2kcoord

open_locale direct_sum
/-
⨁ i, β i is now available as the n-ary direct sum.
 -/

universes u 

-- Let K be any non-empty field
variables 
  (K : Type u)  -- scalar type
  [inhabited K] -- non-empty
  [field K]     -- forms a field

-- Let n by a positive integer dimension
  (n : ℕ)       -- dimension 
  (ng1 : n > 1) -- dim is > 1

/-
Abbreviation for the type of the direct sum (think
product) of n K × K modules. The variable i here is
the index, selected from a finite set (fin) of size n.

lin2k_sum : 
  Π (K : Type u_1) 
  [_inst_1 : inhabited K] 
  [_inst_2 : field K], 
  ℕ → 
  Type u_1
-/
abbreviation lin2k_sum := ⨁(i : fin n), (λi, K × K) i

/-
Proof (by typeclass instantiation) that such a direct
sum of K×K modules over K is also a module.
-/
instance : module K (lin2k_sum K n) := by apply_instance

-- Not sure this is used, and it's broken, so ignore
-- def mk_finset (n : ℕ) : finset (fin n) := sorry
-- def finsetn := mk_finset n
-- def mk_linnk : (fin (n) → K × K) → lin2k_sum K n :=
--   λv, 
--   let val : Π (i : (↑(finsetn (n)) : set (fin (n)))), (λi, K × K) i.val := λi, v i in
--   direct_sum.lmk K _ _ _ (val)
-- def mk_linnk' : (fin (n) → K × K) → lin2k_sum K n :=
--   λv, 
--   let val : Π (i : (↑(finsetn (n)) : set (fin (n)))), (λi, K × K) i.val := λi, v i in
--   direct_sum.lmk K _ _ _ (val)