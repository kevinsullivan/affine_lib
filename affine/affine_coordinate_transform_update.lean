import .affine_coordinate_framed_space_lib --linear_algebra.affine_space.basic
import 
    linear_algebra.affine_space.basic
    linear_algebra.affine_space.affine_equiv 
    linear_algebra.nonsingular_inverse
    linear_algebra.matrix
--    linear_algebra.

open_locale affine

namespace aff_trans

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

variables 
    (sp1 : affine_coord_space K n fr1)
    (sp2 : affine_coord_space K n fr2)
  (a1 : affine_coord_frame_transform K n fr1 fr2)
  (a2 : affine_coord_space_transform K n fr1 fr2 sp1 sp2)


abbreviation
    affine_tuple_space_transform
    := 
    (aff_pt_coord_tuple K n)
    ≃ᵃ[K] 
    (aff_pt_coord_tuple K n)

/-
abbreviation
    affine_coord_space_transform
    (sp1 : affine_coord_space K n fr1)
    (sp2 : affine_coord_space K n fr2)
    := 
    affine_coord_frame_transform K n fr1 fr2
-/
structure 
  affine_tuple_space_tagged_transform
    (K : Type u)
    (n : ℕ)
    [inhabited K] 
    [field K] 
    --{fr1 : affine_coord_frame K n} 
    --{fr2 : affine_coord_frame K n} 
  := 
    (fr1 : affine_coord_frame K n) 
    (fr2 : affine_coord_frame K n) 
    (sp1 : affine_coord_space K n fr1)
    (sp2 : affine_coord_space K n fr2)
    (tr : affine_tuple_space_transform K n)

@[trans] def trans
    (K : Type u)
    (n : ℕ)
    [inhabited K] 
    [field K] 
     (t1 : affine_tuple_space_tagged_transform K n) 
     (t2 : affine_tuple_space_tagged_transform K n) : affine_tuple_space_tagged_transform K n :=
⟨t1.fr1, t2.fr2, t1.sp1, t2.sp2, t1.tr.trans t2.tr⟩ 



def affine_vec_coord_tuple.as_matrix
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (v : aff_vec_coord_tuple K n)
    : col_matrix K n
    :=
    λ i one, (@aff_lib.coord_helper K n v.1).nth i

attribute [reducible]
def affine_pt_coord_tuple.as_matrix
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (v : aff_pt_coord_tuple K n)
    : col_matrix K n
    :=
    λ i one, (@aff_lib.coord_helper K n v.1).nth i

#check fin 3

attribute [reducible]
def affine_coord_vec.to_matrix
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr : affine_coord_frame K n}
    (v : aff_coord_vec K n fr)
    : col_matrix K n
    :=
    affine_vec_coord_tuple.as_matrix v.1
    --λ i one, (@aff_lib.coord_helper K n v.1.1).nth i

attribute [reducible]
def affine_coord_pt.to_matrix
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr : affine_coord_frame K n}
    (v : aff_coord_pt K n fr)
    : col_matrix K n
    :=
    affine_pt_coord_tuple.as_matrix v.1
    --λ i one, (@aff_lib.coord_helper K n v.1.1).nth i

attribute [reducible]
def affine_coord_vec.to_indexed
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr : affine_coord_frame K n}
    (v : aff_coord_vec K n fr)
    : fin n → K
    :=
    λ i, (@aff_lib.coord_helper K n v.1.1).nth i
    --λ i one, (@aff_lib.coord_helper K n v.1.1).nth i

attribute [reducible]
def affine_coord_pt.to_indexed
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr : affine_coord_frame K n}
    (v : aff_coord_pt K n fr)
    : fin n → K 
    :=
    λ i, (@aff_lib.coord_helper K n v.1.1).nth i
    --λ i one, (@aff_lib.coord_helper K n v.1.1).nth i

attribute [reducible]
def affine_vec_coord_tuple.to_indexed
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (v : aff_vec_coord_tuple K n )
    : fin n → K 
    :=
    λ i, (@aff_lib.coord_helper K n v.1).nth i
    --λ i one, (@aff_lib.coord_helper K n v.1.1).nth i

attribute [reducible]
def affine_pt_coord_tuple.to_indexed
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (v : aff_pt_coord_tuple K n )
    : fin n → K 
    :=
    λ i, (@aff_lib.coord_helper K n v.1).nth i

attribute [reducible]
def col_matrix.as_list_helper
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (coords : col_matrix K n)
    : fin n → list K
| ⟨nat.zero,p⟩ := [(coords ⟨nat.zero,p⟩ 1)]
| ⟨nat.succ k,p⟩ := 
    --append current index to result of recursive step and return
    let kp : k < n := begin
      have h₁ : k < k.succ := begin
        rw eq.symm (nat.one_add k),
        simp only [nat.succ_pos', lt_add_iff_pos_left]
      end,
      apply has_lt.lt.trans,
      exact h₁,
      exact p
    end in
    let upd := [(coords ⟨k, kp⟩ 1)] in
    have (⟨k, kp⟩ : fin n) < (⟨k.succ,p⟩ : fin n), from begin
      simp only [subtype.mk_lt_mk],
      rw eq.symm (nat.one_add k),
      simp only [nat.succ_pos', lt_add_iff_pos_left]
    end,
    --have t : a < (a + b), from sorry,
    (col_matrix.as_list_helper ⟨k,kp⟩)++upd --$ λ _, sorry
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λi, i.val)⟩]}

attribute [reducible]
def col_matrix.as_list
  {K : Type u}
  {n : ℕ}
  [inhabited K]
  [field K]
  : col_matrix K n → list K
:= begin
  intro mat,
  cases n with n',
  exact [],
  have h₁ : n' < n'+1 := 
    begin
      by linarith,
    end,
  have h₂ : n'.succ = n'+1 :=
    begin
      simp 
    end,
  have h₃ : n' < n'.succ :=
    begin
      simp [h₁, h₂ ]
    end,
  exact (col_matrix.as_list_helper mat (⟨n',h₃⟩ : fin (nat.succ n'))),
end


attribute [reducible]
def indexed.as_list_helper
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (coords : fin n → K)
    : fin n → list K
| ⟨nat.zero,p⟩ := [(coords ⟨nat.zero,p⟩)]
| ⟨nat.succ k,p⟩ := 
    --append current index to result of recursive step and return
    let kp : k < n := begin
      have h₁ : k < k.succ := begin
        rw eq.symm (nat.one_add k),
        simp only [nat.succ_pos', lt_add_iff_pos_left]
      end,
      apply has_lt.lt.trans,
      exact h₁,
      exact p
    end in
    let upd := [(coords ⟨k, kp⟩)] in
    have (⟨k, kp⟩ : fin n) < (⟨k.succ,p⟩ : fin n), from begin
      simp only [subtype.mk_lt_mk],
      rw eq.symm (nat.one_add k),
      simp only [nat.succ_pos', lt_add_iff_pos_left]
    end,
    --have t : a < (a + b), from sorry,
    (indexed.as_list_helper ⟨k,kp⟩)++upd --$ λ _, sorry
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λi, i.val)⟩]}

attribute [reducible]
def indexed.as_list
  {K : Type u}
  {n : ℕ}
  [inhabited K]
  [field K]
  : (fin n → K) → list K
:= begin
  intro mat,
  cases n with n',
  exact [],
  have h₁ : n' < n'+1 := 
    begin
      by linarith,
    end,
  have h₂ : n'.succ = n'+1 :=
    begin
      simp 
    end,
  have h₃ : n' < n'.succ :=
    begin
      simp [h₁, h₂ ]
    end,
  exact (indexed.as_list_helper mat (⟨n',h₃⟩ : fin (nat.succ n'))),
end

attribute [reducible]
def affine_coord_pt.from_matrix
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (fr : affine_coord_frame K n)
    (coords : col_matrix K n)
    : aff_coord_pt K n fr
    := 
    ⟨⟨[1]++(col_matrix.as_list coords), sorry, rfl⟩⟩

attribute [reducible]
def affine_coord_vec.from_matrix
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (fr : affine_coord_frame K n)
    (coords : col_matrix K n)
    : aff_coord_vec K n fr
    := 
    ⟨⟨[0]++(col_matrix.as_list coords),sorry,rfl⟩⟩

attribute [reducible]
def affine_coord_pt.from_indexed
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (fr : affine_coord_frame K n)
    (coords : fin n → K)
    : aff_coord_pt K n fr
    := 
    ⟨⟨[1]++(indexed.as_list coords),sorry,rfl⟩⟩

attribute [reducible]
def affine_coord_vec.from_indexed
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (fr : affine_coord_frame K n)
    (coords : fin n → K)
    : aff_coord_vec K n fr
    := 
    ⟨⟨[0]++(indexed.as_list coords),sorry,rfl⟩⟩


attribute [reducible]
def affine_pt_coord_tuple.from_indexed
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (coords : fin n → K)
    : aff_pt_coord_tuple K n
    := 
    ⟨[1]++(indexed.as_list coords),sorry,rfl⟩

attribute [reducible]
def affine_vec_coord_tuple.from_indexed
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (coords : fin n → K)
    : aff_vec_coord_tuple K n
    := 
    ⟨[0]++(indexed.as_list coords),sorry,rfl⟩
  
--#check 
--(rfl :(matrix (fin n) (fin 1) K) = (col_matrix K n))
   -- (matrix (fin n) (fin 1) K)=(matrix (fin n) (fin 1) K))

attribute [reducible]
def affine_coord_frame.get_basis_matrix
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


attribute [reducible]
def affine_coord_frame.get_origin_matrix
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (fr : affine_coord_frame K n)
    : col_matrix K n
    := 
    affine_pt_coord_tuple.as_matrix
        (aff_lib.affine_coord_frame.origin_coords 
            fr)

attribute [reducible]
def affine_tuple_coord_frame.get_basis_matrix
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (fr : affine_tuple_coord_frame K n)
    : square_matrix K n
    := 
    λ i j,
    (aff_lib.affine_tuple_vec.get_coords  
    (
        (fr.basis) j))
    .nth i


attribute [reducible]
def affine_tuple_coord_frame.get_origin_matrix
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (fr : affine_tuple_coord_frame K n)
    : col_matrix K n
    := 
    affine_pt_coord_tuple.as_matrix
        (fr.origin)
--def fold_transforms
/-
IS THIS IN MATHLIB ALREADY?
NOT matrix.diag_one??
-/
attribute [reducible]
def square_matrix.eye
    (K : Type u)
    (n : ℕ)
    [inhabited K] 
    [field K] 
    : square_matrix K n
    := 
    λ i j,
    if i = j then 1 else 0
/-
undo coordinates:
(x + B^O)
-/

--#check list.fold
#check list

/-
    (
    ((path.from_.map (λf,aff_fr.affine_coord_frame.tuple f))
        .map affine_coord_frame.to_homogeneous_matrix)
    ++
    (((path.to_.map (λf,aff_fr.affine_coord_frame.tuple f))
        .map affine_coord_frame.to_homogeneous_matrix)
        .map (λh,h⁻¹))
    )
-/



attribute [reducible]
noncomputable def affine_coord_space.to_base_space
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr1 : affine_coord_frame K n}
    (der_sp : affine_coord_space K n fr1)
    : affine_coord_space_transform K n fr1 
                                      (affine_coord_frame.base_frame fr1)
                                      der_sp
                                      (affine_coord_space.get_base_space der_sp)
    := ⟨begin
      cases fr1,
      have h₁ : affine_coord_frame.base_frame (affine_coord_frame.tuple fr1) = affine_coord_frame.standard K n := rfl,
      rw h₁,
      sorry,

      have h₁ : affine_coord_frame.base_frame (affine_coord_frame.derived fr1_origin fr1_basis fr1_proof_is_basis fr1_base) = fr1_base := rfl,
      rw h₁,
      sorry
    end, sorry, sorry⟩

attribute [reducible]
noncomputable def affine_coord_space.to_derived_space
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr1 : affine_coord_frame K n}
    (der_sp : affine_coord_space K n fr1)
    : affine_coord_space_transform K n
                                      (affine_coord_frame.base_frame fr1)
                                      fr1
                                      (affine_coord_space.get_base_space der_sp)
                                      der_sp
    := ⟨ sorry, sorry, sorry⟩
    

attribute [reducible]
noncomputable def affine_coord_space.to_standard_space
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr1 : affine_coord_frame K n}
    (der_sp : affine_coord_space K n fr1)
    : affine_coord_space_transform K n fr1 
                                      (affine_coord_frame.standard K n)
                                      der_sp
                                      (affine_coord_space.mk_with_standard K n)
    := ⟨ sorry, sorry, sorry⟩

    

attribute [reducible]
noncomputable def affine_coord_space.from_standard_space
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr1 : affine_coord_frame K n}
    (der_sp : affine_coord_space K n fr1)
    : affine_coord_space_transform K n
                                      (affine_coord_frame.standard K n )
                                      fr1
                                      (affine_coord_space.mk_with_standard K n)
                                      der_sp
    := ⟨ sorry, sorry, sorry⟩

def affine_coord_space_transform.domain_frame
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr1 : affine_coord_frame K n}
    {from_sp : affine_coord_space K n fr1}
    {fr2 : affine_coord_frame K n}
    {to_sp : affine_coord_space K n fr2}
    (tr : affine_coord_space_transform K n fr1 fr2 from_sp to_sp)
    := fr1

def affine_coord_space_transform.codomain_frame
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr1 : affine_coord_frame K n}
    {from_sp : affine_coord_space K n fr1}
    {fr2 : affine_coord_frame K n}
    {to_sp : affine_coord_space K n fr2}
    (tr : affine_coord_space_transform K n fr1 fr2 from_sp to_sp)
    := fr2

def affine_coord_space_transform.domain_space
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr1 : affine_coord_frame K n}
    {from_sp : affine_coord_space K n fr1}
    {fr2 : affine_coord_frame K n}
    {to_sp : affine_coord_space K n fr2}
    (tr : affine_coord_space_transform K n fr1 fr2 from_sp to_sp)
    := from_sp
/-
def affine_coord_space_transform.codomain_space
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr1 : affine_coord_frame K n}
    {from_sp : affine_coord_space K n fr1}
    {fr2 : affine_coord_frame K n}
    {to_sp : affine_coord_space K n fr2}
    (tr : affine_coord_space_transform K n fr1 fr2 from_sp to_sp)
-/

variables (a_1 a_2 : aff_pt_coord_tuple K n)

#check a_1 -ᵥ a_2

attribute [reducible]
noncomputable def affine_tuple_space.to_base_space
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
   -- [affine_space (aff_vec_coord_tuple K n) (aff_pt_coord_tuple K n)]
    (fr : affine_tuple_coord_frame K n)
    : affine_tuple_space_transform K n
    :=
    ⟨
      ⟨
        λ p ,
          ((fr.origin -ᵥ pt_zero K n) : aff_vec_coord_tuple K n) +ᵥ
          (affine_pt_coord_tuple.from_indexed
            (
              (
                matrix.mul_vec 
                (affine_tuple_coord_frame.get_basis_matrix fr)
                (affine_pt_coord_tuple.to_indexed p)
              ) --: fin n → K
            )
          ),
        λ p,
          (vec_neg K n (affine_vec_coord_tuple.from_indexed
            (
              (
                matrix.mul_vec 
                (affine_tuple_coord_frame.get_basis_matrix fr)
                (affine_vec_coord_tuple.to_indexed 
                  ((fr.origin -ᵥ pt_zero K n) : aff_vec_coord_tuple K n))
              ) --: fin n → K
            )
          )) +ᵥ
          (affine_pt_coord_tuple.from_indexed
            (
              (
                matrix.mul_vec 
                (affine_tuple_coord_frame.get_basis_matrix fr)⁻¹
                (affine_pt_coord_tuple.to_indexed p)
              ) --: fin n → K
            )
          ),
          sorry,
          sorry
      ⟩,
      ⟨
        λ v,
          (affine_vec_coord_tuple.from_indexed
            (
              (
                matrix.mul_vec 
                (affine_tuple_coord_frame.get_basis_matrix fr)
                (affine_vec_coord_tuple.to_indexed v)
              ) --: fin n → K
            )
          )
            ,
        sorry,
        sorry,
        λ v,
          (affine_vec_coord_tuple.from_indexed
            (
              (
                matrix.mul_vec 
                (affine_tuple_coord_frame.get_basis_matrix fr)⁻¹
                (affine_vec_coord_tuple.to_indexed v)
              ) --: fin n → K
            )
          ),
        sorry,
        sorry⟩ ,
      sorry
    ⟩




attribute [reducible]
noncomputable def affine_tuple_space.to_derived_space
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
   -- [affine_space (aff_vec_coord_tuple K n) (aff_pt_coord_tuple K n)]
    (fr : affine_tuple_coord_frame K n)
    : affine_tuple_space_transform K n
    := 
    (affine_tuple_space.to_base_space fr)⁻¹ 

attribute [reducible]
noncomputable def affine_tuple_space.standard_transform
  := 
  affine_tuple_space.to_derived_space (affine_tuple_coord_frame.standard K n)

attribute [reducible]
noncomputable def affine_tuple_space.to_base_space_tagged
    {fr1 : affine_coord_frame K n}
    (from_sp : affine_coord_space K n fr1)
    {fr2 : affine_coord_frame K n}
    (to_sp : affine_coord_space K n fr2)
    : affine_tuple_space_tagged_transform K n
    := ⟨fr1, fr2, from_sp, to_sp, affine_tuple_space.to_base_space (affine_coord_frame.get_coords fr1)⟩


attribute [reducible]
noncomputable def affine_tuple_space.to_derived_space_tagged
    {fr1 : affine_coord_frame K n}
    (from_sp : affine_coord_space K n fr1)
    {fr2 : affine_coord_frame K n}
    (to_sp : affine_coord_space K n fr2)
    : affine_tuple_space_tagged_transform K n
    := ⟨fr1, fr2, from_sp, to_sp, affine_tuple_space.to_derived_space (affine_coord_frame.get_coords fr2)⟩

attribute [reducible]
noncomputable def affine_tuple_space_transform.to_coord_transform
    {fr1 : affine_coord_frame K n}
    (from_sp : affine_coord_space K n fr1)
    {fr2 : affine_coord_frame K n}
    (to_sp : affine_coord_space K n fr2)
    (tr : affine_tuple_space_transform K n)
    :
    affine_coord_space_transform K n fr1 fr2 from_sp to_sp
    := 
    ⟨
      ⟨
        λ p,⟨tr p.1⟩ ,
        λ p,⟨tr⁻¹ p.1⟩,
        sorry,
        sorry 
      ⟩ ,
      ⟨
        λ v,⟨tr.linear v.1⟩,
        sorry,
        sorry,
        λ v,⟨tr.linear⁻¹ v.1⟩,
        sorry,
        sorry
      ⟩,
      sorry
    ⟩

attribute [reducible]
noncomputable mutual def 
  affine_coord_space.build_from_to_standard_transform,
  affine_coord_space.fold_tuple_from_to_standard_transforms
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {initial_fr : affine_coord_frame K n}
    (initial_sp : affine_coord_space K n initial_fr)
with affine_coord_space.build_from_to_standard_transform : 
  list (aff_fr.affine_coord_frame K n) → 
                                  (affine_coord_space_transform K n
                                      initial_fr
                                      (affine_coord_frame.standard K n)
                                      initial_sp
                                      (affine_coord_space.mk_with_standard K n))
| [] := 
  let tr := (affine_tuple_space.to_base_space (affine_coord_frame.get_coords initial_fr)) in
    affine_tuple_space_transform.to_coord_transform K n _ _ tr
| (h::t) := 
  let tr := (affine_tuple_space.to_base_space (affine_coord_frame.get_coords initial_fr)) in 
  let trf := tr.trans (affine_coord_space.fold_tuple_from_to_standard_transforms t) in
    affine_tuple_space_transform.to_coord_transform K n _ _ tr
with affine_coord_space.fold_tuple_from_to_standard_transforms :
  list (aff_fr.affine_coord_frame K n) → 
                                  (affine_tuple_space_transform K n)
| [] := (affine_tuple_space.standard_transform K n )
| (h::t) := let tr := (affine_tuple_space.to_base_space (affine_coord_frame.get_coords initial_fr)) in 
      tr.trans 
          (affine_coord_space.fold_tuple_from_to_standard_transforms t)

attribute [reducible]
noncomputable mutual def 
  affine_coord_space.build_standard_to_to_transform,
  affine_coord_space.fold_tuple_to_to_standard_transforms
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {to_fr : affine_coord_frame K n}
    (to_sp : affine_coord_space K n to_fr)
with affine_coord_space.build_standard_to_to_transform : 
  list (aff_fr.affine_coord_frame K n) → 
                                  (affine_coord_space_transform K n
                                      (affine_coord_frame.standard K n)
                                      to_fr
                                      (affine_coord_space.mk_with_standard K n))
                                      to_sp
| [] := 
  let tr := (affine_tuple_space.to_base_space (affine_coord_frame.get_coords to_fr)) in
    ((affine_tuple_space_transform.to_coord_transform K n to_sp (affine_coord_space.mk_with_standard K n) tr).symm)
| (h::t) := 
  let tr := (affine_tuple_space.to_derived_space (affine_coord_frame.get_coords to_fr)) in 
  let trf := tr.trans (affine_coord_space.fold_tuple_to_to_standard_transforms t) in
    (affine_tuple_space_transform.to_coord_transform K n to_sp (affine_coord_space.mk_with_standard K n) tr).symm
with affine_coord_space.fold_tuple_to_to_standard_transforms :
  list (aff_fr.affine_coord_frame K n) → 
                                  (affine_tuple_space_transform K n)
| [] := (affine_tuple_space.standard_transform K n )
| (h::t) := 
  let tr := (affine_tuple_space.to_derived_space (affine_coord_frame.get_coords to_fr)) in 
      tr.trans 
          (affine_coord_space.fold_tuple_to_to_standard_transforms t)

attribute [reducible]
noncomputable def affine_coord_space.build_transform
    [inhabited (affine_coord_frame K n)]
    (sp1 : affine_coord_space K n fr1)
    (sp2 : affine_coord_space K n fr2)
    : affine_coord_space_transform K n fr1 fr2 sp1 sp2
    := 
    let path := affine_coord_space.find_transform_path' sp1 sp2 in
    --let from_head_eq_fr1 : fr1 = path.from_.head := sorry in
    --let to_head_eq_fr2 : fr2 = path.to_.head := sorry in
    let from_ := (affine_coord_space.build_from_to_standard_transform sp1 path.to_.tail) in
    let to_ := (affine_coord_space.build_standard_to_to_transform sp2 path.to_.tail) in
      from_.trans to_

    --([] : list (square_matrix K (n+1)))

notation t1⬝t2 := t1.trans t2
notation t1•t2 := t1.trans t2

variables 
    (fr3 : affine_coord_frame K n)
    (s1 : affine_coord_space K n fr1)
    (s2 : affine_coord_space K n fr2)
    (s3 : affine_coord_space K n fr3)
    (t1 : affine_coord_space_transform K n fr1 fr2 s1 s2)
    (t2 : affine_coord_space_transform K n fr2 fr3 s2 s3)
    (p1 : aff_coord_pt K n fr1)
    (p2 : aff_coord_pt K n fr2)
#check t1⬝t2

#check t1 p1
#check t1 p2  -- There is supposed to be an error here. It means the type-checking is working!

def tran_times_vec 
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr1 : affine_coord_frame K n}
   -- (from_sp : affine_coord_space K n fr1)
    {fr2 : affine_coord_frame K n}
   -- (to_sp : affine_coord_space K n fr2)
   (tr : affine_coord_frame_transform K n fr1 fr2)
   (p : aff_coord_vec K n fr1)
   : aff_coord_vec K n fr2
   := tr (p +ᵥ (⟨pt_zero K n⟩ : aff_coord_pt K n fr1))
        -ᵥ (⟨pt_zero K n⟩ : aff_coord_pt K n fr2)

#check t1.trans

notation t1⬝t2 := tran_times_vec t1 t2
notation t1⬝t2 := t1.to_equiv t2

end aff_trans