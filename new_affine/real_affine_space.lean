import linear_algebra.affine_space.basic
import ..new_affine.affine_coordinate_space
import data.real.basic


abbreviation real_vec := aff_vec ℝ
abbreviation real_pt  := aff_pt  ℝ

abbreviation r3_vec := real_vec 3
abbreviation r3_pt  := real_pt  3

universes u v w

structure aff_struct :=
(X : Type u)
(K : Type v)
(V : Type w)
(fld : ring K)
(grp : add_comm_group V)
(vec : module K V)
(aff : affine_space V X)

structure vec_struct :=
(K : Type u)
(V : Type v)
(fld : field K)
(grp : add_comm_group V)
(vec : vector_space K V)

inductive Algebra  
| aff_space (a : aff_struct)
| vec_space (v : vec_struct)
| nat_monoid -- placeholder, commutative monoid with monus operator

noncomputable def to_affine : ℕ → aff_struct := λ n,
    ⟨aff_pt ℝ n, ℝ, aff_vec ℝ n, real.ring, aff_comm_group ℝ n, aff_module ℝ n, aff_coord_is ℝ n⟩


noncomputable def to_vector : ℕ → vec_struct := λ n, 
    ⟨ℝ, aff_vec ℝ n, real.field, aff_comm_group ℝ n, aff_module ℝ n⟩