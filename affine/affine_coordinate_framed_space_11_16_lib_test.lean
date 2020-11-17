import data.real.basic
import .affine_coordinate_framed_space_11_16_lib
--import .real_affine_coordinate_space_lib

noncomputable theory

open aff_lib

def Rn := aff_lib.affine_coord_space.mk_with_standard ℝ 3

def Rn_pt1 := aff_lib.affine_coord_space.mk_point Rn ⟨[0,0,0], by refl⟩
def Rn_vec1 := aff_lib.affine_coord_space.mk_vec Rn ⟨[1,0,0], by refl⟩
def Rn_vec2 := aff_lib.affine_coord_space.mk_vec Rn ⟨[0,1,0], by refl⟩
def Rn_vec3 := aff_lib.affine_coord_space.mk_vec Rn ⟨[0,0,1], by refl⟩

def origin : _ := affine_coord_space.origin Rn

-- TO DO NEXT
-- def frame : _ := affine_coord_nspace.frame Rn
-- def origin : _ := frame.origin --Rn

#check origin
def basis := affine_coord_space.basis Rn
/-

def vecsub := r3_der2_vec1 - r3_der2_vec2 -- expected :pass
def vecptadd := r3_der2_pt1 +ᵥ r3_der2_vec2 --expected : pass
def ptvecadd := r3_der2_vec2 +ᵥ r3_der2_pt1 --expected : pass
def vecptsub := r3_der2_pt1 -ᵥ r3_der2_vec2 --expected : pass
def ptvecsub := r3_der2_vec2 -ᵥ r3_der2_pt1 -- expected : pass
def pt_sub := r3_der2_pt1 - r3_der2_pt1 -- expected : pass
def pt_add := r3_der2_pt1 + r3_der2_pt1 -- expected : fail
def dif_fr := r3_der1_vec1 - r3_der2_vec2 -- expected : fail

-/
#check origin
#check basis 1 -ᵥ basis 2 --expected : pass
#check basis 1 +ᵥ basis 2 --expected : pass
#check origin +ᵥ origin --expected : fail
#check origin -ᵥ origin --expected : pass
#check basis 1 
#check basis 1 -ᵥ origin --expected : fail
#check origin -ᵥ basis 2 --expected : pass?
#check origin +ᵥ basis 2 --expected : pass



def Rn_pt1' := aff_lib.affine_coord_space.mk_point Rn ⟨[1,1,1], by refl⟩
def Rn_vec1' := aff_lib.affine_coord_space.mk_vec Rn ⟨[2,0,0], by refl⟩
def Rn_vec2' := aff_lib.affine_coord_space.mk_vec Rn ⟨[0,2,0], by refl⟩
def Rn_vec3' := aff_lib.affine_coord_space.mk_vec Rn ⟨[0,0,2], by refl⟩
--combine derived frame func into mk derived space

def der_fr := affine_coord_space.mk_frame 
    Rn 
    Rn_pt1' 
    (λ i : fin 3, vector.nth (⟨[Rn_vec1', Rn_vec3', Rn_vec2'], sorry⟩ : vector _ 3) i)
    sorry

#check option

def der_sp := affine_coord_space.mk_derived_from_coords Rn (affine_coordinate_frame.get_coords der_fr)

def der_origin := affine_coord_space.origin der_sp
def der_basis := affine_coord_space.basis der_sp

#check der_basis 1 +ᵥ basis 2
#check der_basis 2 +ᵥ der_basis 2
#check der_basis 1 -ᵥ basis 1
#check der_origin -ᵥ der_origin
#check der_origin -ᵥ origin


def base_Rn_fr := affine_coordinate_frame.base_frame 
                    (affine_coord_space.frame Rn)

def base_der_sp_fr := affine_coordinate_frame.base_frame 
                    (affine_coord_space.frame der_sp)

def base_Rn := affine_coord_space.get_base_space Rn

def base_der_sp := affine_coord_space.get_base_space der_sp


def base_vec := affine_coord_space.mk_vec base_der_sp ⟨[0,0,0], by refl⟩

#check base_vec +ᵥ basis 2 -- expected: pass or no??

#check (affine_coord_space.frame base_der_sp)
--#reduce (affine_coord_space.frame base_der_sp)
