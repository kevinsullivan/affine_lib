import .aff_coord_space .affine .list_stuff data.real.basic

universes u v w 

variables (X : Type u) (K : Type v) (V : Type w) (n : ℕ) (k : K)
[inhabited K] [field K] [add_comm_group V] [vector_space K V] [affine_space X K V]

abbreviation zero := list.field_zero K n

def to_std_basis : ℕ → list K := λ x, (zero K n).update_nth x 1

variable [field ℤ]

#check to_std_basis K n

def std_basis : fin n → aff_vec K n :=
λ x, ⟨to_std_basis K n x.1, sorry, sorry⟩

