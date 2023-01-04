/-
© 2021 by the Rector and Visitors of the University of Virginia
-/

/-
In this file we construct a typeclass instance
carrying a proof of the lemma that if K is a 
non-empty field then K × K has the structure 
of a module. The rationale for this construction
is that (currently) we're representing 1-d affine
space points and vectors as 2-d linear vectors,
in the usual manner.
-/


import algebra.module.basic
import linear_algebra.affine_space.affine_equiv

-- Let K be the carrier set of an arbitrary non-empty field
universes u 
variables 
  (K : Type u) 
  [field K] 
  [inhabited K]

-- 
lemma add_smul_l2 : 
  ∀ (r s : K) (x : K × K), (r + s) • x = r • x + s • x := 
begin
  intros,
  ext,
  simp *,
  exact right_distrib r s _,
  simp *,
  exact right_distrib r s _,
end

lemma zero_smul_l2 : ∀ (x : K × K), (0 : K) • x = 0 := 
begin
  intros,
  ext,
  simp *,
  simp *,
end

-- lemma proved by construction of typeclass instance
instance module_K_KxK : module K (K × K) := 
⟨ add_smul_l2 K, zero_smul_l2 K ⟩ 

