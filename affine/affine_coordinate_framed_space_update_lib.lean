import .affine_coordinate_framed_space_update
import .affine_space_type
import .list_as_k_tuple
universes u v w
/-
This file defines the following types:
affine_coord_space
affine_tuple_basis
affine_coord_basis
transform_path

affine_coord_frame.standard 
affine_coord_frame.base_frame 
affine_coord_frame.origin_coords
affine_coord_frame.basis_coords 
affine_coord_space.origin
affine_coord_space.basis
affine_coord_space.frame
affine_coord_space.standard_space
affine_coord_space.mk_with_standard
affine_coord_space.get_base_space
affine_coord_space.mk_coord_point
affine_coord_space.mk_coord_vec
affine_coord_space.mk_point
affine_coord_space.mk_vec
affine_coord_space.mk_basis
affine_coord_space.mk_frame
affine_coord_space.mk_tuple_frame
affine_coord_space.mk_derived
affine_coord_frame.get_coords
affine_coord_space.mk_derived_from_coords
affine_coord_space.mk_from_frame

affine_coord_frame.build_path
affine_coord_space.find_transform_path
-/

namespace aff_lib

open aff_fr
variables 
    (K : Type v) 
    (n : ℕ) 
    [inhabited K] 
    [field K] 
    --(fr : affine_tuple_coord_frame K n)
    (fr : affine_coord_frame K n)

def affine_coord_space :=
    affine_space_type 
        (aff_coord_pt K n fr)
        K
        (aff_coord_vec K n fr)

def affine_tuple_basis :=
    (fin n) → aff_vec_coord_tuple K n

def affine_coord_basis :=
    (fin n) → aff_coord_vec K n fr

/-
Helper method to retrieve the origin of coord space defined in
terms of a particular frame (which has an origin that we need to retrieve)
-/

abbreviation zero := vecl.zero_vector K n

def list.to_basis_vec : fin n → list K := λ x, (zero K n).update_nth (x.1 + 1) 1

lemma len_basis_vec_fixed (x : fin n) : (list.to_basis_vec K n x).length = n + 1 := sorry

lemma head_basis_vec_fixed (x : fin n) : (list.to_basis_vec K n x).head = 0 := sorry

def std_basis : fin n → aff_vec_coord_tuple K n :=
λ x, ⟨list.to_basis_vec K n x, len_basis_vec_fixed K n x, head_basis_vec_fixed K n x⟩

def affine_coord_frame.standard : affine_coord_frame K n := 
    (affine_coord_frame.tuple ⟨pt_zero K n, std_basis K n, sorry⟩)

def affine_coord_frame.base_frame 
    {K : Type v}
    {n : ℕ}
    [inhabited K] 
    [field K] 
: affine_coord_frame K n → affine_coord_frame K n
| (affine_coord_frame.tuple base) := affine_coord_frame.standard K n
| (affine_coord_frame.derived _ _ _ fr) := fr

def affine_coord_frame.origin_coords
    {K : Type v}
    {n : ℕ}
    [inhabited K] 
    [field K] 
     : affine_coord_frame K n → aff_pt_coord_tuple K n
| (affine_coord_frame.tuple base) := base.origin
| (affine_coord_frame.derived o _ _ _) := o


def affine_coord_frame.basis_coords 
    {K : Type v}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    : affine_coord_frame K n → affine_tuple_basis K n
| (affine_coord_frame.tuple base) := base.basis
| (affine_coord_frame.derived _ b _ _) := b

/-
Helper method to retrieve the origin of ℕ-indexed coord space defined in
terms of a particular frame (which has an origin that we need to retrieve)
-/
def affine_coord_space.origin
    {K : Type v}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr : affine_coord_frame K n}
    (sp : affine_coord_space K n fr)
    : aff_coord_pt K n (affine_coord_frame.base_frame fr)
    :=
        ⟨affine_coord_frame.origin_coords (affine_coord_frame.base_frame fr)⟩

/-
Helper method to retrieve the basis of coord space defined in
terms of a particular frame (which has a basis that we need to retrieve)
-/
def affine_coord_space.basis
    {K : Type v}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr : affine_coord_frame K n}
    (sp : affine_coord_space K n fr)
    : affine_coord_basis K n (affine_coord_frame.base_frame fr)
    :=
        λ i : fin n, ⟨(affine_coord_frame.basis_coords (affine_coord_frame.base_frame fr)) i⟩


def affine_coord_space.frame
    {K : Type v}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr : affine_coord_frame K n}
    (sp : affine_coord_space K n fr)
    := 
        fr

abbreviation affine_coord_space.standard_space
    := affine_coord_space K n (affine_coord_frame.standard K n)

def affine_coord_space.mk_with_standard
    : affine_coord_space.standard_space K n
    := ⟨⟩


def affine_coord_space.get_base_space
    {K : Type v}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr : affine_coord_frame K n}
    (sp : affine_coord_space K n fr)
    : affine_coord_space K n (affine_coord_frame.base_frame fr)
    :=
        ⟨⟩

def affine_coord_space.mk_coord_point
    {K : Type v}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr : affine_coord_frame K n}
    (sp : affine_coord_space K n fr)
    (val : vector K n)
    : aff_pt_coord_tuple K n
    := ⟨[1]++val.1,sorry,sorry⟩

def affine_coord_space.mk_coord_vec
    {K : Type v}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr : affine_coord_frame K n}
    (sp : affine_coord_space K n fr)
    (val : vector K n)
    : aff_vec_coord_tuple K n
    := ⟨[0]++val.1,sorry,sorry⟩

def affine_coord_space.mk_point
    {K : Type v}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr : affine_coord_frame K n}
    (sp : affine_coord_space K n fr)
    (val : vector K n)
    : aff_coord_pt K n fr
    := ⟨⟨[1]++val.1,sorry,sorry⟩⟩

def affine_coord_space.mk_vec
    {K : Type v}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr : affine_coord_frame K n}
    (sp : affine_coord_space K n fr)
    (val : vector K n)
    : aff_coord_vec K n fr
    := ⟨⟨[0]++val.1,sorry,sorry⟩⟩

    --:= ⟨⟩

/-
slight issue here, 
because the type of a derived frame does not contain the original frame,
i don't raise an explicit type error if the space's frame and frame's base frame don't match
fix for now is just to supply a coord tuple frame
-/
def affine_coord_space.mk_basis
    {K : Type v}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr : affine_coord_frame K n}
    (sp : affine_coord_space K n fr)
    (vecs : vector (aff_coord_vec K n fr) n)
     : affine_coord_basis K n fr
    := 
        λ i : fin n, vecs.nth i
    

def affine_coord_space.mk_frame
    {K : Type v}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr : affine_coord_frame K n}
    (sp : affine_coord_space K n fr)
    (pt : aff_coord_pt K n fr)
    (basis : affine_coord_basis K n fr)
    
    := 
        (affine_coord_frame.derived pt.1 (λ i:fin n,(basis i).1) sorry)


def affine_coord_space.mk_tuple_frame
    {K : Type v}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr : affine_coord_frame K n}
    (sp : affine_coord_space K n fr)
    (pt : aff_coord_pt K n fr)
    (basis : affine_coord_basis K n fr)
    : affine_tuple_coord_frame K n
    := 
        ⟨pt.1, (λ i:fin n,(basis i).1),sorry⟩

def affine_coord_space.mk_derived
    {K : Type v}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr : affine_coord_frame K n}
    (sp : affine_coord_space K n fr)
    (pt : aff_coord_pt K n fr)
    (basis : affine_coord_basis K n fr)
    : affine_coord_space K n 
        (affine_coord_frame.derived pt.1 (λ i:fin n,(basis i).1) sorry fr)
    := ⟨⟩

def affine_coord_frame.get_coords
    {K : Type v}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    : affine_coord_frame K n → affine_tuple_coord_frame K n
| (affine_coord_frame.tuple b) := b
| (affine_coord_frame.derived o b _ _) := ⟨o,b,sorry⟩

def affine_coord_space.mk_derived_from_coords
    {K : Type v}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr : affine_coord_frame K n}
    (sp : affine_coord_space K n fr)
    (f : affine_tuple_coord_frame K n)
    : affine_coord_space K n 
        (affine_coord_frame.derived f.1 (λ i:fin n,(f.2 i)) sorry fr)
    := ⟨⟩

def affine_coord_space.mk_from_frame
    {K : Type v}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (fr : affine_coord_frame K n)
    : affine_coord_space K n fr 
    := ⟨ ⟩

structure transform_path
    {K : Type v}
    {n : ℕ}
    [inhabited K] 
    [field K] :=
    mk:: 
    (from_ : list (affine_tuple_coord_frame K n))
    (to_ : list (affine_tuple_coord_frame K n))

def affine_coord_frame.build_path
    {K : Type v}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    :  affine_coord_frame K n → list (affine_tuple_coord_frame K n)
| (affine_coord_frame.tuple b) := [b]
| (affine_coord_frame.derived o b p f) := ⟨o,b,p⟩::(affine_coord_frame.build_path f)

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
    := ⟨affine_coord_frame.build_path fr1, affine_coord_frame.build_path fr2⟩



end aff_lib