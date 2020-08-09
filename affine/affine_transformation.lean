import .aff_coord_space

universes u v w

variables (X : Type u) (K : Type v) (V : Type w) (n : ℕ) (id : ℕ) (k : K)
[inhabited K] [field K] [add_comm_group V] [vector_space K V] [affine_space X K V]

#check linear_map

structure aff_auto :=
(f_v : V → V) 
(f_p : X → X)
(linear_map : ∃ g : linear_map K V V, ∀ v : V, ∃ x : V, f_v v = g v + x)

structure aff_coord_map :=
(f_v : aff_vec K n → aff_vec K n)
(f_p : aff_pt K n → aff_pt K n)
(linear_part : ∃ g : linear_map K (aff_vec K n) (aff_vec K n), ∀ v : aff_vec K n, ∃ x, f_v v = g v + x)

structure aff_coord_map' :=
(to_fun : affine_space X K V → affine_space X K V) -- doesn't work. maps one prop to another.

