import .aff_coord_space
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
(fld : field K)
(grp : add_comm_group V)
(vec : vector_space K V)
(aff : affine_space X K V)

structure vec_struct :=
(K : Type u)
(V : Type v)
(fld : field K)
(grp : add_comm_group V)
(vec : vector_space K V)

inductive Algebra  
| affine_space (a : aff_struct)
| vector_space (v : vec_struct)
| nat_monoid -- placeholder, commutative monoid with monus operator

noncomputable def to_affine : ℕ → aff_struct := λ n,
    ⟨aff_pt ℝ n, ℝ, aff_vec ℝ n, real.field, aff_comm_group ℝ n, aff_vec_space ℝ n, aff_coord_is ℝ n⟩


noncomputable def to_vector : ℕ → vec_struct := λ n, 
    ⟨ℝ, aff_vec ℝ n, real.field, aff_comm_group ℝ n, aff_vec_space ℝ n⟩