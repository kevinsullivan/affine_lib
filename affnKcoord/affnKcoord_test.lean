import .affnKcoord

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

def v3 := (1/4)•v2 +ᵥ (mk_vectr std_sp ⟨[-1,0,1], rfl⟩)

def der_fm1 : fm K first_id dim := fm.deriv 
  p2.coords 
  (λi, match i.1 with
    | 0 := v1.coords
    | 1 := v2.coords
    | _ := v3.coords
    end)
  std_fm

def der_sp1 : spc der_fm1 := mk_space der_fm1

def der_fm2 : fm K first_id dim := fm.deriv 
  p2.coords 
  (λi, match i.1 with
    | 0 := v2.coords
    | 1 := v3.coords
    | _ := v1.coords
    end)
  std_fm

def der_sp2 : spc der_fm2 := mk_space der_fm2

def der_vec1 : vectr der_sp1 := mk_vectr _ ⟨[1,2,3],rfl⟩

def der_vec2 : vectr der_sp2 := mk_vectr _ ⟨[1,2,3],rfl⟩

def bad_sp_add := der_vec1 +ᵥ der_vec2

def der1_to_2 := der_sp1.fm_tr der_sp2

def trans_der_vec1 : vectr der_sp2 := der1_to_2.transform_vectr der_vec1

def okay_sp_add : _ := (der1_to_2.transform_vectr der_vec1) +ᵥ der_vec2


