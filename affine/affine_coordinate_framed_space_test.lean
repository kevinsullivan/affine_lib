import .affine_coordinate_framed_space
import .affine_space_type
import data.real.basic
import linear_algebra.affine_space.basic
import .affine_coordinate_space_lib

noncomputable theory
open aff_fr


/-
Given an arbitrary affine space, return (turn it 
into) an affine coordinate space by specifying a
point in as.X to serve as the origin and a basis
in terms of as.V to serve as a basis.
-/

--structure affine_coordinate_space_type

--def mk_raw 
--    ⟨ ⟩ 
--def mk_real_n := mk_raw standard...

--def mk_der

/-
inductive affine_coordinate_space_type
| mk_raw (as : affine_space aff_pt K aff_vec) (o : origin) 
| mk_der (acs : affine_coordinate_space_type) (acf: affine_coordinate_frame)
-/

/-
def ra3cs := affine_coord_space_type.mk_raw 
    (as : affine_space) -- a "raw" affine space, no frame
    (o : origin)        -- a "raw" point in as.X to serve as origin
    (b: basis)          -- a set of "raw" basis vectors from as.V

def framed_origin := ra3cs.get_framed_origin    -- get me framed origin point
def framed_vector_0 := ra3cs.get_framed_basis_vector 0    -- get me first framed basis vector
def new_framed_point := framed_origin + framed_vector

def new_frame := frame.mk new_framed_point <framed_vector_0, ..., >
def new_point_new_frame := point.mk new_frame <coods> 
-/

/-
sp_derived_n ...
sp_derived_n.origin : (aff_coord_pt fr_n-1)


-/


abbreviation r3_vec := (aff_vec_coord_tuple ℝ 3)
abbreviation r3_pt := (aff_pt_coord_tuple ℝ 3)
def r3_std : affine_frame (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) := aff_coord_space_std_frame ℝ 3

#check r3_std

abbreviation r3_fr_vec := aff_coord_vec r3_pt ℝ r3_vec 3 (fin 3) r3_std
abbreviation r3_fr_pt := aff_coord_pt r3_pt ℝ r3_vec 3 (fin 3) r3_std

def aff1 : affine_space_type r3_pt ℝ r3_vec := ⟨⟩ 

def aff_coord1 : affine_coord_space_type 3 r3_std := ⟨⟩ --???

def o := aff_coord1.fr.origin

def aff2 : affine_space_type r3_fr_pt ℝ r3_fr_vec := ⟨⟩

def r3_vec1 : r3_vec := ⟨[0,1,0,0],sorry,sorry⟩
def r3_vec2 : r3_vec := ⟨[0,0,1,0],sorry,sorry⟩
def r3_vec3 : r3_vec := ⟨[0,0,0,1],sorry,sorry⟩
def r3_pt1 : r3_pt := ⟨[1,0,0,0],sorry,sorry⟩

def r3_fr_vec1 : r3_fr_vec := ⟨r3_vec3⟩
def r3_fr_vec2 : r3_fr_vec := ⟨r3_vec1⟩
def r3_fr_vec3 : r3_fr_vec := ⟨r3_vec2⟩
def r3_fr_pt1 : r3_fr_pt := ⟨r3_pt1⟩

def to_basis (n:ℕ) {pty : Type*} (l : vector pty n) := 
    λ i : fin n, l.nth i
 
def der1 : affine_frame r3_fr_pt ℝ r3_fr_vec (fin 3) := 
    ⟨r3_fr_pt1,to_basis 3 ⟨[r3_fr_vec1,r3_fr_vec2,r3_fr_vec3],sorry⟩,sorry⟩

abbreviation r3_der1_vec := 
    aff_coord_vec r3_fr_pt ℝ r3_fr_vec 3 (fin 3) der1
abbreviation r3_der1_pt := 
    aff_coord_pt r3_fr_pt ℝ r3_fr_vec 3 (fin 3) der1

def r3_der1_vec1 : r3_der1_vec := ⟨r3_vec2⟩
def r3_der1_vec2 : r3_der1_vec := ⟨r3_vec3⟩
def r3_der1_vec3 : r3_der1_vec := ⟨r3_vec1⟩
def r3_der1_pt1 : r3_der1_pt := ⟨r3_pt1⟩

def der2 : affine_frame r3_der1_pt ℝ r3_der1_vec (fin 3) := 
    ⟨r3_der1_pt1,to_basis 3 ⟨[r3_der1_vec1,r3_der1_vec2,r3_der1_vec3],sorry⟩,sorry⟩
    

abbreviation r3_der2_vec := 
    aff_coord_vec r3_der1_pt ℝ r3_der1_vec 3 (fin 3) der2
abbreviation r3_der2_pt := 
    aff_coord_pt r3_der1_pt ℝ r3_der1_vec 3 (fin 3) der2

def r3_der2_vec1 : r3_der2_vec := ⟨r3_vec2⟩
def r3_der2_vec2 : r3_der2_vec := ⟨r3_vec3⟩
def r3_der2_vec3 : r3_der2_vec := ⟨r3_vec1⟩
def r3_der2_pt1 : r3_der2_pt := ⟨r3_pt1⟩

def vecsub := r3_der2_vec1 - r3_der2_vec2 -- expected :pass
def vecptadd := r3_der2_pt1 +ᵥ r3_der2_vec2 --expected : pass
def ptvecadd := r3_der2_vec2 +ᵥ r3_der2_pt1 --expected : pass
def vecptsub := r3_der2_pt1 -ᵥ r3_der2_vec2 --expected : pass
def ptvecsub := r3_der2_vec2 -ᵥ r3_der2_pt1 -- expected : pass
def pt_sub := r3_der2_pt1 -ᵥ r3_der2_pt1 -- expected : pass
def pt_add := r3_der2_pt1 +ᵥ r3_der2_pt1 -- expected : fail
def dif_fr := r3_der1_vec1 - r3_der2_vec2 -- expected : fail

def scaled : r3_der2_vec2  := (1:ℝ)•r3_der2_vec2 
