import linear_algebra.affine_space.basic
import ..new_affine.affine_coordinate_space
import data.real.basic


namespace real_affine

abbreviation real_vec := aff_vec ℝ
abbreviation real_pt  := aff_pt  ℝ

abbreviation r3_vec := real_vec 3
abbreviation r3_pt  := real_pt  3

universes u v w

structure aff_struct 
    (dim : ℕ)
    (X : Type u)
    (K : Type v)
    (V : Type w)
    [ring K] 
    [add_comm_group V] 
    [module K V]  
    [affine_space V X]
--(vec : add_comm_group V)
--(vs : module K V)
--(aff : affine_space V X)
--(fr : affine_frame  X K V (fin dim))
open aff_fr

structure aff_vec_struct 
    (dim : ℕ)
    (X : Type u)
    (K : Type v)
    (V : Type w)
    [ring K] 
    [add_comm_group V] 
    [module K V]  
    [affine_space V X]
    :=
    (aff_sp : aff_struct dim X K V)
    (vec : V)

structure aff_pt_struct 
    (dim : ℕ)
    (X : Type u)
    (K : Type v)
    (V : Type w)
    [ring K] 
    [add_comm_group V] 
    [module K V]  
    [affine_space V X]:=
    (aff_sp : aff_struct dim X K V)
    (pt : X)

structure aff_fr_struct
    (dim : ℕ)
    (X : Type u)
    (K : Type v)
    (V : Type w)
    [ring K] 
    [add_comm_group V] 
    [module K V]  
    [affine_space V X]:=
    --(aff_sp : aff_struct dim X K V)
    (aff_fr : affine_frame X K V (fin dim))

/-
structure aff_struct 
    (dim : ℕ)
    (X : Type u)
    (K : Type v)
    (V : Type w)
     :=--[aff_coord_is X K V]:=
(fld : ring K)
(grp : add_comm_group V)
(vec : module K V)
(aff : affine_space V X)
(fr : affine_frame  X K V (fin dim))
-/

structure vec_struct (dim : ℕ) :=
(K : Type u)
(V : Type v)
(fld : field K)
(grp : add_comm_group V)
(vec : vector_space K V)

inductive Algebra  
| aff_space 
    {dim : ℕ} {X : Type} {K : Type} {V : Type} 
    [ring K] 
    [add_comm_group V] 
    [module K V]  
    [affine_space V X] (a : aff_struct dim X K V)
| aff_vector 
    {dim : ℕ} {X : Type} {K : Type} {V : Type} 
    [ring K] 
    [add_comm_group V] 
    [module K V]  
    [affine_space V X] (a : aff_vec_struct dim X K V)
| aff_point
    {dim : ℕ} {X : Type} {K : Type} {V : Type} 
    [ring K] 
    [add_comm_group V] 
    [module K V]  
    [affine_space V X] (a : aff_pt_struct dim X K V)
| aff_frame 
    {dim : ℕ} {X : Type} {K : Type} {V : Type} 
    [ring K] 
    [add_comm_group V] 
    [module K V]  
    [affine_space V X] (a : aff_fr_struct dim X K V)
| vec_space (dim : ℕ) (v : vec_struct dim)
| nat_monoid -- placeholder, commutative monoid with monus operator

def get_vecl : ℕ → list ℝ
| (nat.succ n) := (0:ℝ) :: get_vecl n
| 0 := []

def get_e_i (dim : ℕ) : list ℝ → ℕ → list ℝ
| l (nat.succ n) := if nat.succ n = dim then (1:ℝ) :: l else (0:ℝ) :: l
| l (nat.zero) := l

def get_zero_pt (dim : ℕ) : aff_pt ℝ dim := ⟨get_vecl dim, sorry, sorry⟩

def vector_copy_helper {dim : ℕ} : vector ℝ dim → ℕ → list ℝ → list ℝ 
| v (nat.succ n) l := [(v.nth (⟨n,sorry⟩ : fin dim))]++(vector_copy_helper v n l)
| v (nat.zero) l := l
--| v idx l := if idx = dim then (1:ℝ)::l else (vector_copy_helper v idx-1 l)++[(v.nth (⟨idx,sorry⟩ : fin dim))]
def vector_to_vec_list {dim : ℕ} : vector ℝ dim → list ℝ
| v := 0::(vector_copy_helper v.reverse dim []).reverse

def vector_to_pt_list {dim : ℕ} : vector ℝ dim → list ℝ
| v := 1::(vector_copy_helper v.reverse dim []).reverse
--| v idx l := if idx = dim then (1:ℝ)::l else (vector_to_pt_list v idx l)++[(v.nth (⟨idx,sorry⟩ : fin dim))]

def vector_to_vec {dim : ℕ} : vector ℝ dim → aff_vec ℝ dim 
    := λv, ⟨vector_to_vec_list v, sorry, sorry⟩

def vector_to_pt {dim : ℕ} : vector ℝ dim → aff_pt ℝ dim 
    := λv, ⟨vector_to_pt_list v, sorry, sorry⟩

def get_basis (dim : ℕ) : fin dim → aff_vec ℝ dim :=
    λ (n : fin dim), ⟨get_e_i dim ([] : list ℝ) dim, sorry, sorry⟩

def get_standard_frame_on_Rn (dim : ℕ) : affine_frame  (aff_pt ℝ dim) ℝ (aff_vec ℝ dim) (fin dim) :=
    affine_frame.standard (get_zero_pt dim) (get_basis dim) sorry

abbreviation real_affine_point_with_frame (dim : ℕ) := 
    pt_with_frame (aff_pt ℝ dim) ℝ (aff_vec ℝ dim) (fin dim) 
abbreviation real_affine_vector_with_frame (dim : ℕ) := 
    vec_with_frame (aff_pt ℝ dim) ℝ (aff_vec ℝ dim) (fin dim) 

abbreviation r_fr (dim : ℕ) :=
    affine_frame  (aff_pt ℝ dim) ℝ (aff_vec ℝ dim) (fin dim)
abbreviation real_affine_frame (dim : ℕ) := 
    --affine_frame  (aff_pt ℝ dim) ℝ (aff_vec ℝ dim) (fin dim)
    aff_fr_struct dim (aff_pt ℝ dim) ℝ (aff_vec ℝ dim) 
--abbreviation derived_fr {dim : ℕ} := affine_frame  (aff_pt ℝ dim) ℝ (aff_vec ℝ dim) (fin dim)

abbreviation real_affine_vector (dim : ℕ) :=
    aff_vec_struct dim (aff_pt ℝ dim) ℝ (aff_vec ℝ dim) 

abbreviation real_affine_point (dim : ℕ) :=
    aff_pt_struct dim (aff_pt ℝ dim) ℝ (aff_vec ℝ dim) 

abbreviation real_affine_space (dim : ℕ) := 
    aff_struct dim (aff_pt ℝ dim) ℝ (aff_vec ℝ dim)


abbreviation real_coordinatized_affine_space {dim : ℕ} (fr : r_fr dim) :=
     aff_struct dim (real_affine_point_with_frame dim fr) ℝ (real_affine_vector_with_frame dim fr)
abbreviation real_affine_coordinatized_vector  {dim : ℕ} (fr : r_fr dim) :=
     aff_vec_struct dim (real_affine_point_with_frame dim fr) ℝ (real_affine_vector_with_frame dim fr)
abbreviation real_affine_coordinatized_point  {dim : ℕ} (fr : r_fr dim) :=
     aff_pt_struct dim (real_affine_point_with_frame dim fr) ℝ (real_affine_vector_with_frame dim fr)

def real_affine_space.get_standard_frame {dim : ℕ} --{f : real_affine_frame dim} 
    (sp : real_affine_space dim)
    : r_fr dim
:= get_standard_frame_on_Rn dim --⟨get_zero_pt dim, get_basis dim, sorry⟩

def real_affine_coordinate_space.get_coordinate_frame {dim : ℕ} {f : r_fr dim} 
    (sp : real_coordinatized_affine_space f)
    : r_fr dim 
:= f

def real_affine_coordinate_space.change_coordinate_frame {dim : ℕ} {f : r_fr dim}
    (original : real_coordinatized_affine_space f)
    (origin : vector ℝ dim) 
    (basis : fin dim → (vector ℝ dim) ) :=
    real_coordinatized_affine_space 
        (affine_frame.derived 
            (aff_pt.mk (vector_to_pt_list origin) sorry sorry)
             (λ x: fin dim, ⟨vector_to_vec_list (basis x),sorry,sorry⟩) sorry f)

def to_affine_space (n : ℕ) : real_affine_space n :=
    ⟨⟩
    --⟨aff_pt ℝ n, ℝ, aff_vec ℝ n, real.ring, aff_comm_group ℝ n, aff_module ℝ n, aff_coord_is ℝ n⟩
def to_coordinatized_affine_space (n : ℕ) (fr : r_fr n) : real_coordinatized_affine_space fr :=--(get_standard_frame_on_Rn n) := 
    ⟨⟩ --⟨real.ring, prf_real_add_comm_grp_n n,prf_vec_module_n n,prf_aff_crd_sp n, get_standard_frame n⟩

def to_affine_vector {n : ℕ} (v : vector ℝ n) : real_affine_vector n :=
    ⟨to_affine_space n, vector_to_vec v⟩

def to_affine_point {n : ℕ} (v : vector ℝ n) : real_affine_point n :=
    ⟨to_affine_space n, vector_to_pt v⟩

def to_standard_frame (n : ℕ) : real_affine_frame n :=
    ⟨real_affine_space.get_standard_frame (to_affine_space n)⟩

def to_derived_frame
    (n : ℕ) (p : vector ℝ n) (b : fin n → vector ℝ n) 
    {fr : r_fr n} 
    (sp : real_coordinatized_affine_space fr) :
    real_affine_frame n :=
    ⟨affine_frame.derived (vector_to_pt p) (λi : fin n,vector_to_vec (b i)) sorry fr⟩
    
def to_affine_vector_with_frame {n : ℕ} (v : vector ℝ n)
    {fr : r_fr n} 
    (sp : real_coordinatized_affine_space fr) :
    real_affine_coordinatized_vector fr :=
    ⟨sp,  ⟨(vector_to_vec v)⟩⟩


def to_affine_point_with_frame {n : ℕ} (v : vector ℝ n)
    {fr : r_fr n} 
    (sp : real_coordinatized_affine_space fr) :
    real_affine_coordinatized_point fr :=
    ⟨sp,  ⟨(vector_to_pt v)⟩⟩

end real_affine