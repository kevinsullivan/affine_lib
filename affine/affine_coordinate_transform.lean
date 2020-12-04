import .affine_coordinate_framed_space_lib --linear_algebra.affine_space.basic
import 
    linear_algebra.affine_space.affine_equiv 
    linear_algebra.nonsingular_inverse
    linear_algebra.matrix
--    linear_algebra.

open aff_fr
open aff_lib
universes u 
variables 
    (K : Type u)
    (n : ℕ )
    [inhabited K]
    [field K]
    (fr1 : affine_coord_frame K n) 
    (fr2 : affine_coord_frame K n) 
    (cv1 cv2 : aff_coord_vec K n fr1) 
    (cp1 cp2 : aff_coord_pt  K n fr2)

/-

def affine_coord_frame.build_path
    {K : Type v}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    :  affine_coord_frame K n → 
        list (affine_tuple_coord_frame K n)
| (affine_coord_frame.tuple b) := [b]
| (affine_coord_frame.derived o b p f) := 
    ⟨o,b,p⟩::(affine_coord_frame.build_path f)

def affine_coord_space.find_transform_path
    {K : Type v}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr1 : affine_coord_frame K n}
    (from_sp : affine_coord_space K n fr1)
    {fr2 : affine_coord_frame K n}
    (to_sp : affine_coord_space K n fr2)
    : transform_path
    := ⟨affine_coord_frame.build_path fr1, 
    affine_coord_frame.build_path fr2⟩

-/
attribute [reducible]
abbreviation square_matrix
    (K : Type u)
    (n : ℕ)
    [inhabited K] 
    [field K] 
    := matrix (fin n) (fin n ) K
 
attribute [reducible]
abbreviation col_matrix
    (K : Type u)
    (n : ℕ)
    [inhabited K] 
    [field K] 
    := matrix (fin n) (fin 1) K
   

abbreviation 
    affine_coord_frame_transform 
    := 
    (aff_coord_pt K n fr1) 
    ≃ᵃ[K] 
    (aff_coord_pt K n fr2)

abbreviation
    affine_coord_space_transform
    (sp1 : affine_coord_space K n fr1)
    (sp2 : affine_coord_space K n fr2)
    := 
    affine_coord_frame_transform K n fr1 fr2

def affine_coord_vec.as_matrix
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr : affine_coord_frame K n}
    (v : aff_coord_vec K n fr)
    : col_matrix K n
    :=
    λ i one, (@aff_lib.coord_helper K n v.1.1).nth i

def affine_coord_pt.as_matrix
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr : affine_coord_frame K n}
    (v : aff_coord_pt K n fr)
    : col_matrix K n
    :=
    λ i one, (@aff_lib.coord_helper K n v.1.1).nth i

#check 
(rfl :(matrix (fin n) (fin 1) K) = (col_matrix K n))
   -- (matrix (fin n) (fin 1) K)=(matrix (fin n) (fin 1) K))
/-
instance 
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr : affine_coord_frame K n}
    : has_lift (aff_coord_pt K n fr)
                (matrix (fin n) (fin 1) K)
    := ⟨affine_coord_pt.as_matrix⟩ 
instance 
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr : affine_coord_frame K n}
    : has_lift (aff_coord_vec K n fr)
                (matrix (fin n) (fin 1) K)
    := ⟨affine_coord_vec.as_matrix⟩ 
-/
/-
invalid definition, a declaration named 'matrix.has_lift' has already been declaredL
-/

def m : matrix (fin n) (fin n) K
    := λ i j, 1

def affine_coord_frame.to_basis_matrix
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (fr : affine_coord_frame K n)
    : square_matrix K n
    := 
    λ i j,
    (aff_lib.affine_tuple_vec.get_coords  
    (
        (aff_lib.affine_coord_frame.basis_coords 
            fr) j))
    .nth i

--def fold_transforms

def affine_coord_space.to_transform
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr1 : affine_coord_frame K n}
    (from_sp : affine_coord_space K n fr1)
    {fr2 : affine_coord_frame K n}
    (to_sp : affine_coord_space K n fr2)
    : affine_coord_space_transform K n fr1 fr2 from_sp to_sp
    :=

/-
def affine_coord_frame.to_equiv
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (fr : affine_coord_frame K n)
    :-/
/-
structure equiv (α : Sort*) (β : Sort*) :=
(to_fun    : α → β)
(inv_fun   : β → α)
(left_inv  : left_inverse inv_fun to_fun)
(right_inv : right_inverse inv_fun to_fun)

structure affine_equiv (k P₁ P₂ : Type*) {V₁ V₂ : Type*} [ring k]
  [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁]
  [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] extends P₁ ≃ P₂ :=
(linear : V₁ ≃ₗ[k] V₂)
(map_vadd' : ∀ (p : P₁) (v : V₁), to_equiv (v +ᵥ p) = linear v +ᵥ to_equiv p)
-/