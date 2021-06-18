import .affnKcoord_transforms

abbreviation K := ℚ 
def dim := 3
def first_id := 1
def std_fm : fm K dim first_id := fm.base dim first_id
def std_sp := mk_space std_fm
#check std_fm

def p1 : point std_sp := 
  mk_point std_sp (⟨[1,2,3], rfl⟩ : vector K 3)

def p1c : fin dim → pt K := p1.coords

--def p1alt : point std_sp :=


#check p1.coords

def v1 : vectr std_sp :=
  mk_vectr _ ⟨[2,5,8], rfl⟩

def p2 := 3•v1 +ᵥ p1

def bad_point_add := p2 +ᵥ p2 

def v2 := p2 -ᵥ p1

def v3 := (1/4 : ℚ)•v2 +ᵥ (mk_vectr std_sp ⟨[-1,0,1], rfl⟩)

#eval (1/4)•4

def vecd : vec K := (1/4 : K)•(mk_vec K 6)
#eval vecd

def der_fm1 : fm K dim first_id := fm.deriv 
  p2.coords 
  (λi, match i.1 with
    | 0 := v1.coords
    | 1 := v2.coords
    | _ := v3.coords
    end)
  sorry sorry std_fm

def my_pt : point std_sp := mk_point std_sp ⟨[1,1,1],rfl⟩

--def u4 : vectr std_sp := mk_vectr std_sp ⟨[1,2,-1],rfl⟩
--def u5 : vectr std_sp := mk_vectr std_sp ⟨[-2,0,1],rfl⟩
--def u6 : vectr std_sp := mk_vectr std_sp ⟨[1,-1,0],rfl⟩

def u4 : vectr std_sp := mk_vectr std_sp ⟨[6,0,0],rfl⟩
def u5 : vectr std_sp := mk_vectr std_sp ⟨[0,6,0],rfl⟩
def u6 : vectr std_sp := mk_vectr std_sp ⟨[0,0,6],rfl⟩

def myder : fm K dim first_id
    := fm.deriv my_pt.coords (λi, match i.1 with
    | 0 := u4.coords
    | 1 := u5.coords
    | _ := u6.coords
    end) sorry sorry std_sp.fm 


def mydersp := mk_space myder

def pt2 := mk_point mydersp ⟨[1,1,1],rfl⟩

def tfd : point std_sp := (mydersp.fm_tr std_sp).transform_point pt2

#eval tfd.coords ⟨2, sorry⟩


def homder := myder.to_homogeneous_matrix

/-
WARNING : ALL MATRIX EVALUATION BROKEN AS OF 6/17 DUE TO INTRODUCTION OF 
LINEAR INDEPENDENCE AND SPANNING PROOFS IN FM.DERIV DEFINITION

THIS MUST BE SOLVED OR REMOVED IN ORDER TO EVALUATE TRANSFORM RESULTS OR 
COORDINATES OF MATRICES.
-/


#check v1.coords
#eval p2.coords ⟨3,sorry⟩
#eval v1.coords ⟨2,sorry⟩
#eval v2.coords ⟨2,sorry⟩
#eval v3.coords ⟨0,sorry⟩
#eval homder 2 3

#eval homder ⟨0,sorry⟩ ⟨0,sorry⟩
#eval homder 1 0
#eval homder 2 0
#eval homder 3 0
#eval homder 0 1
#eval homder 1 1
#eval homder 2 1
#eval homder 3 1
#eval homder 0 2
#eval homder 1 2
#eval homder 2 2
#eval homder 3 2
#eval homder 0 3
#eval homder 1 3
#eval homder 2 3
#eval homder 3 3

def homder_inv := homder.cramer_inverse

#eval homder_inv ⟨0,sorry⟩ ⟨0,sorry⟩
#eval homder_inv 1 0
#eval homder_inv 2 0
#eval homder_inv 3 0
#eval homder_inv 0 1
#eval homder_inv 1 1
#eval homder_inv 2 1
#eval homder_inv 3 1
#eval homder_inv 0 2
#eval homder_inv 1 2
#eval homder_inv 2 2
#eval homder_inv 3 2
#eval homder_inv 0 3
#eval homder_inv 1 3
#eval homder_inv 2 3
#eval homder_inv 3 3

def inv_mul := homder_inv.mul homder

#check inv_mul
#eval inv_mul ⟨0,sorry⟩ ⟨0,sorry⟩
#eval inv_mul 1 0
#eval inv_mul 2 0
#eval inv_mul 3 0
#eval inv_mul 0 1
#eval inv_mul 1 1
#eval inv_mul 2 1
#eval inv_mul 3 1
#eval inv_mul 0 2
#eval inv_mul 1 2
#eval inv_mul 2 2
#eval inv_mul 3 2
#eval inv_mul 0 3
#eval inv_mul 1 3
#eval inv_mul 2 3
#eval inv_mul 3 3

#eval homder 0 0






def der_sp1 : spc K der_fm1 := mk_space der_fm1

def der_fm2 : fm K dim first_id := fm.deriv 
  p2.coords 
  (λi, match i.1 with
    | 0 := v2.coords
    | 1 := v3.coords
    | _ := v1.coords
    end)
  sorry sorry std_fm

def der_sp2 : spc K der_fm2 := mk_space der_fm2

def der_vec1 : vectr der_sp1 := mk_vectr _ ⟨[1,2,3],rfl⟩

def der_vec2 : vectr der_sp2 := mk_vectr _ ⟨[1,2,3],rfl⟩

def bad_sp_add := der_vec1 +ᵥ der_vec2

def der1_to_2 := der_sp1.fm_tr der_sp2

def trans_der_vec1 : vectr der_sp2 := der1_to_2.transform_vectr der_vec1

def okay_sp_add : _ := (der1_to_2.transform_vectr der_vec1) +ᵥ der_vec2

#check (der_vec1.expressed_in der_sp2)


