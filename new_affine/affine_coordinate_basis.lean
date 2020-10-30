import .affine_coordinate_space .list_as_k_tuple 
import data.real.basic linear_algebra.affine_space.basic
import linear_algebra.basis

/-
This file imports affine_coordinate_space, which, in turn
imports affine_with_frame.
-/

universes u v w x

variables (X : Type u) (K : Type v) (V : Type w) (n : ℕ) (k : K)
[inhabited K] [field K] [add_comm_group V] [vector_space K V] [affine_space V X]

open vecl

abbreviation zero := zero_vector K n

def list.to_basis_vec : fin n → list K := λ x, (zero K n).update_nth (x.1 + 1) 1

lemma len_basis_vec_fixed (x : fin n) : (list.to_basis_vec K n x).length = n + 1 := sorry

lemma head_basis_vec_fixed (x : fin n) : (list.to_basis_vec K n x).head = 0 := sorry

def std_basis : fin n → aff_vec K n :=
λ x, ⟨list.to_basis_vec K n x, len_basis_vec_fixed K n x, head_basis_vec_fixed K n x⟩

lemma std_is_basis : is_basis K (std_basis K n) := sorry

/-
A stamdard frame is an affine frame using the standard zero
point as an origin and the standard unit basis vectors as a
basis.
-/
def std_frame : affine_frame (aff_pt K n) K (aff_vec K n) (fin n) := 
    ⟨pt_zero K n, std_basis K n, std_is_basis K n⟩

-- noncomputable def r3_std_frame := std_frame ℝ 3
-- def std_origin : pt_with_frame (aff_pt K n) K (aff_vec K n) (fin n) (std_frame K n) := pt_zero K n