import linear_algebra.affine_space.basic
import ..new_affine.affine_coordinate_space
import ..new_affine.affine_coordinate_basis
import data.real.basic
import .real_affine_space



inductive Algebra  
| aff_space 
    {dim : ℕ} {X : Type} {K : Type} {V : Type} 
    [ring K] 
    [add_comm_group V] 
    [module K V]  
    [affine_space V X] (a : real_affine.affine_space_type dim X K V)
| nat_monoid -- placeholder, commutative monoid with monus operator
