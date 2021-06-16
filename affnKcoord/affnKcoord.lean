import .affnK
import linear_algebra.affine_space.affine_equiv
import linear_algebra.matrix

/-
Framed points, vectors, frames
-/

open_locale affine
universes u 

section explicitK

variables 
(K : Type u) [field K] [inhabited K]
(space_id : ℕ) (dim : ℕ) 

def id_vec : fin dim → ℕ := λi, space_id

inductive fm (K : Type u) [inhabited K] [field K] : Πdim : ℕ, Πid_vec:fin dim → ℕ, Type u
| base : Πdim : ℕ, Πid_vec:fin dim → ℕ, fm dim id_vec
| deriv 
    {dim : ℕ}
    {id_vec : fin dim → ℕ}
    (origin : pt_n K dim) 
    (basis : fin dim → vec_n K dim)
    (parent : fm dim id_vec)
    : fm dim id_vec
| prod
    (dim1 dim2 : ℕ)
    (id1 : fin dim1 → ℕ)
    (id2 : fin dim2 → ℕ)
    (f1 : fm dim1 id1)
    (f2 : fm dim2 id2)
    (prod_origin : pt_n K (dim1 + dim2))
    (prod_basis : fin (dim1+dim2) → vec_n K (dim1 + dim2))
    : fm (dim1+dim2) (add_maps id1 id2)

attribute [reducible]
def fm.parent2
{K : Type u} [field K] [inhabited K]
{dim : ℕ} {id_vec : fin dim → ℕ} :
fm K dim id_vec → fm K dim id_vec
| (fm.base dim id_vec) := (fm.base dim id_vec)
| (fm.deriv origin basis parent) := parent
| (fm.prod d1 d2 i1 i2 f1 f2 o1 b1 : fm K dim id_vec) := (fm.prod f1 f2)


def fm.parent 
{K : Type u} [field K] [inhabited K]
{dim : ℕ} {id_vec : fin dim → ℕ}
(f: fm K dim id_vec) : fm K dim id_vec:=
begin
    cases f,
    exact (fm.base dim id_vec),
    exact f_parent,
    exact fm.prod f_f1 f_f2 f_prod_origin f_prod_basis
end
/-| (fm.base dim id_vec) := (fm.base dim id_vec)
| (fm.deriv origin basis parent) := parent
| (fm.prod f1 f2) := (fm.prod f1 f2)
-/

def fm.origin2 
{K : Type u} [field K] [inhabited K]
{dim : ℕ} {id_vec : fin dim → ℕ}  :
fm K dim id_vec → pt_n K dim
| (fm.base dim id_vec) := (λi, mk_pt K 0)
| (fm.deriv origin basis parent) := origin
| (fm.prod f1 f2) := (λi, mk_pt K 0)

def fm.origin 
{K : Type u} [field K] [inhabited K]
{dim : ℕ} {id_vec : fin dim → ℕ} 
(f : fm K dim id_vec) : pt_n K dim :=
begin 
    cases f,
    exact (λi, mk_pt K 0),
    exact f_origin,
    exact f_prod_origin
end

def fm.basis 
{K : Type u} [field K] [inhabited K]
{dim : ℕ} {id_vec : fin dim → ℕ} 
(f : fm K dim id_vec) : fin dim → vec_n K dim
:=
begin
    cases f,
    exact (λ i j, if j = i then mk_vec K 1 else mk_vec K 0),
    exact f_basis,
    exact f_prod_basis

end
/-
inductive fm : nat → Type u
| base : ∀ (n : nat), fm n
| deriv : ∀ (n : nat), (prod (pt K) (vec K)) → fm n → fm n
-/

#check fm K 

def mk_fm  {dim : ℕ} {id_vec : fin dim → ℕ}  (p : pt_n K dim) (v : fin dim → vec_n K dim) (f : fm K dim id_vec)
    : fm K dim id_vec:= fm.deriv p v f

def mk_prod_fm
    {K : Type u} [inhabited K] [field K] 
    {dim1 : ℕ} {id_vec1 : fin dim1 → ℕ} (f1 : fm K dim1 id_vec1)
    {dim2 : ℕ} {id_vec2 : fin dim2 → ℕ} (f2 : fm K dim2 id_vec2)
    : fm K (dim1+dim2) (add_maps id_vec1 id_vec2)
    := fm.prod f1 f2 
        (add_maps f1.origin f2.origin) 
        (λi, 
            if i.1 < dim1 then (add_maps (f1.basis ⟨i.1,sorry⟩) (mk_vec_n K dim2 ⟨list.repeat dim2 0, sorry⟩))
            else (add_maps (mk_vec_n K dim1 ⟨list.repeat dim1 0, sorry⟩) (f2.basis ⟨i.1,sorry⟩)))

--structure spc {K : Type u} [inhabited K] [field K] {space_id : nat} {dim : ℕ} (f : fm K dim id_vec) : Type u       -- interesting specimen, here, btw

inductive spc : Π{dim : ℕ}, Π{id_vec : fin dim → ℕ},Π(f: fm K dim id_vec), Type u
| single {dim : ℕ} {id_vec : fin dim → ℕ} (f: fm K dim id_vec) : spc f
| prod 
    {dim1 : ℕ} {id_vec1 : fin dim1 → ℕ} (f1: fm K dim1 id_vec1) --(s1 : spc dim1 id_vec1 f1)
    {dim2 : ℕ} {id_vec2 : fin dim2 → ℕ} (f2: fm K dim2 id_vec2) --(s2 : spc dim2 id_vec2 f2)
    : spc (mk_prod_fm f1 f2)


def spc.fm {K : Type u} [inhabited K] [field K] {dim : ℕ} {id_vec : fin dim → ℕ} {f: fm K dim id_vec} (sp : spc K f)
    := f


--| prod ()

--notation s1`×`s2 := spc.prod s1 s2

def mk_space  {K : Type u} [inhabited K] [field K] 
{dim : ℕ} {id_vec : fin dim → ℕ} 
    (f : fm K dim id_vec) : spc K f  :=
  spc.single f

def mk_prod_spc
    {K : Type u} [inhabited K] [field K] 
    {dim1 : ℕ} {id_vec1 : fin dim1 → ℕ} {f1 : fm K dim1 id_vec1} (s1 : spc K f1)
    {dim2 : ℕ} {id_vec2 : fin dim2 → ℕ} {f2 : fm K dim2 id_vec2} (s2 : spc K f2)
    : spc K (mk_prod_fm f1 f2) := spc.prod f1 f2



/-
inductive prod_spc (K : Type u) [inhabited K] [field K] : Type u
| single  {space_id : nat} {dim : ℕ} {f : fm K dim id_vec} : prod_spc
| double {space_id1 : nat} {dim1 : ℕ} {f1 : fm K space_id1 dim1} {space_id2 : nat} {dim2 : ℕ} {f2 : fm K space_id2 dim2} 
    (s1 : prod_spc) (s2 : prod_spc)
     : prod_spc

def prod_spc.to_spc : prod_spc K → spc -/



end explicitK

section implicitK

variables 
{K : Type u} [field K] [inhabited K] 
{dim : nat} {id_vec : fin dim → nat }{f : fm K dim id_vec} (s : spc K f)
{dim2 : nat } {id_vec2 : fin dim2 → nat} {f2 : fm K dim2 id_vec2} (s2 : spc K f2)

/-
Augment pt and vec types with spaces and frames and
then make operations apply only for objects in same
space (and thus frame).
-/
@[ext]
structure point {f : fm K dim id_vec} (s : spc K f) :=
(coords : pt_n K dim)

@[simp]
def mk_point' (p : pt_n K dim) : point s := point.mk p  

@[simp]
def mk_point (coords_ : vector K dim) : point s := point.mk (mk_pt_n K dim coords_)  

@[simp]
def mk_point_prod  
    {dim : ℕ} {id_vec : fin dim → ℕ} {f: fm K dim id_vec} {s : spc K f}  
    {dim2 : ℕ} {id_vec2 : fin dim2 → ℕ} {f2: fm K dim2 id_vec2} {s2 : spc K f2} 
    
    (p1 : point s) (p2 : point s2) : point (mk_prod_spc s s2)
    := ⟨add_maps p1.coords p2.coords⟩

@[simp]
def point.space {dim : ℕ} {id_vec : fin dim → ℕ} {f: fm K dim id_vec} {s : spc K f} 
    (p : point s) : spc K _ := s

@[ext]
structure vectr {f : fm K dim id_vec} (s : spc K f) :=
(coords : vec_n K dim)

@[simp]
def mk_vectr' (p : vec_n K dim) : vectr s := vectr.mk p  
@[simp]
def mk_vectr (coords_ : vector K dim) : vectr s := vectr.mk (mk_vec_n K dim coords_)  

@[simp]
def mk_vectr_prod 
    {dim : ℕ} {id_vec : fin dim → ℕ} {f: fm K dim id_vec} {s : spc K f}  
    {dim2 : ℕ} {id_vec2 : fin dim2 → ℕ} {f2: fm K dim2 id_vec2} {s2 : spc K f2} 
    (p1 : vectr s) (p2 : vectr s2) : vectr (mk_prod_spc s s2)
    := ⟨add_maps p1.coords p2.coords⟩

@[simp]
def vectr.space {dim : ℕ} {id_vec : fin dim → ℕ} {f: fm K dim id_vec} {s : spc K f} 
    (v : vectr s) : spc K _ := s


-- note that we don't extend fm
def mk_frame {f : fm K dim id_vec} {s : spc K f}  (p : point s) (v : fin dim → vectr s) :=
fm.deriv p.coords (λi, (v i).coords) f   -- TODO: make sure v ≠ 0 (erasing tyoe info)
                                      -- TODO: snd arg is really a basis for the vs


/-
    *************************************
    Instantiate module K (vector K)
    *************************************
-/

variables v1 v2 : vectr s

@[simp]
def add_vectr_vectr (v1 v2 : vectr s) : vectr s :=  mk_vectr' s (v1.coords + v2.coords)
@[simp]
def smul_vectr (k : K) (v : vectr s) : vectr s := mk_vectr' s (k • v.coords)
@[simp]
def neg_vectr (v : vectr s) : vectr s := mk_vectr' s ((-1 : K) • v.coords)
@[simp]
def sub_vectr_vectr (v1 v2 : vectr s) : vectr s := add_vectr_vectr s v1 (neg_vectr s v2)

-- See unframed file for template for proving module

instance has_add_vectr : has_add (vectr s) := ⟨add_vectr_vectr s⟩
lemma add_assoc_vectr : ∀ a b c : vectr s, a + b + c = a + (b + c) := 
begin
    intros,
    ext,
    --cases a,
    repeat {
    have p1 : (a + b + c).coords = a.coords + b.coords + c.coords := rfl,
    have p2 : (a + (b + c)).coords = a.coords + (b.coords + c.coords) := rfl,
    rw [p1,p2],
    cc
    },
    admit,
    admit
end


instance add_semigroup_vectr : add_semigroup (vectr s) := ⟨ add_vectr_vectr s, add_assoc_vectr s⟩ 

@[simp]
def vectr_zero := mk_vectr s ⟨list.repeat 0 dim, sorry⟩--@mk_vectr K _ _ n f s (0:K)
instance has_zero_vectr : has_zero (vectr s) := ⟨vectr_zero s⟩

#check mul_zero_class.zero

lemma zero_add_vectr : ∀ a : vectr s, 0 + a = a := 
begin
    admit/-intros,--ext,
    ext,
    let h0 : (0 + a).coords = (0 : vectr s).coords + a.coords := rfl,
    simp [h0],
    exact zero_add _,
    exact zero_add _,
    -/
end

lemma add_zero_vectr : ∀ a : vectr s, a + 0 = a := 
begin
    admit/-intros,ext,
    exact add_zero _,
    exact add_zero _,-/
end

@[simp]
def nsmul_vectr : ℕ → (vectr s) → (vectr s) 
| nat.zero v := vectr_zero s
--| 1 v := v
| (nat.succ n) v := (add_vectr_vectr _) v (nsmul_vectr n v)

instance add_monoid_vectr : add_monoid (vectr s) := ⟨ 
    -- add_semigroup
    add_vectr_vectr s, 
    add_assoc_vectr s, 
    -- has_zero
    vectr_zero s,
    -- new structure 
    zero_add_vectr s, 
    add_zero_vectr s,
    nsmul_vectr s
⟩

instance has_neg_vectr : has_neg (vectr s) := ⟨ neg_vectr s ⟩
instance has_sub_vectr : has_sub (vectr s) := ⟨ sub_vectr_vectr s ⟩ 
lemma sub_eq_add_neg_vectr : ∀ a b : vectr s, a - b = a + -b := 
begin
    intros,ext,
    refl,refl

end 


instance sub_neg_monoid_vectr : sub_neg_monoid (vectr s) :=
{
    neg := neg_vectr s,
    ..(show add_monoid (vectr s), by apply_instance)
}

/- ⟨ 
    add_vectr_vectr s, add_assoc_vectr s, vectr_zero s, zero_add_vectr s, add_zero_vectr s, -- add_monoid
    neg_vectr s,                                                                  -- has_neg
    sub_vectr_vectr s,                                                              -- has_sub
    sub_eq_add_neg_vectr s,                                                       -- new
⟩ -/

lemma add_left_neg_vectr : ∀ a : vectr s, -a + a = 0 := 
begin
    intros,
    ext,/-
    repeat {
    have h0 : (-a + a).coords = -a.coords + a.coords := rfl,
    simp [h0],
    have : (0:vec K) = (0:vectr s).coords := rfl,
    simp *,
    } -/
    admit,
    admit
end


instance : add_group (vectr s) := {
    add_left_neg := begin
        exact add_left_neg_vectr s,
    end,
..(show sub_neg_monoid (vectr s), by apply_instance),

}


/-⟨
    -- sub_neg_monoid
    add_vectr_vectr s, add_assoc_vectr s, vectr_zero s, zero_add_vectr s, add_zero_vectr s, -- add_monoid
    neg_vectr s,                                                                  -- has_neg
    sub_vectr_vectr s,                                                              -- has_sub
    sub_eq_add_neg_vectr s, 
    -- new
    add_left_neg_vectr s,
⟩ -/

lemma add_comm_vectr : ∀ a b : vectr s, a + b = b + a := 
begin
    intros,
    ext,
    repeat {
    have p1 : (a + b).coords = a.coords + b.coords:= rfl,
    have p2 : (b + a).coords = b.coords + a.coords := rfl,
    rw [p1,p2],
    cc
    } ,
    admit,
    admit   
end

instance add_comm_semigroup_vectr : add_comm_semigroup (vectr s) := ⟨
    -- add_semigroup
    add_vectr_vectr s, 
    add_assoc_vectr s,
    add_comm_vectr s,
⟩

instance add_comm_monoid_vectr : add_comm_monoid (vectr s) := 
{
    add_comm := begin
        exact add_comm_vectr s
    end, 
    ..(show add_monoid (vectr s), by apply_instance)
}



instance has_scalar_vectr : has_scalar K (vectr s) := ⟨
smul_vectr s,
⟩

lemma one_smul_vectr : ∀ b : vectr s, (1 : K) • b = b := begin
    intros,ext,
    repeat {
        have h0 : ((1:K) • b).coords = ((1:K)•(b.coords)) := rfl,
        rw [h0],
        simp *,
    }
end

lemma mul_smul_vectr : ∀ (x y : K) (b : vectr s), (x * y) • b = x • y • b :=
begin
    intros,
    cases b,
    ext,
    exact mul_assoc x y _,
    exact mul_assoc x y _
end

instance mul_action_vectr : mul_action K (vectr s) := ⟨
one_smul_vectr s,
mul_smul_vectr s,
⟩ 

lemma smul_add_vectr : ∀(r : K) (x y : vectr s), r • (x + y) = r • x + r • y := begin
    intros, ext,
    repeat {
    have h0 : (r • (x + y)).coords = (r • (x.coords + y.coords)) := rfl,
    have h1 : (r•x + r•y).coords = (r•x.coords + r•y.coords) := rfl,
    rw [h0,h1],
    simp *,
    }

end

lemma smul_zero_vectr : ∀(r : K), r • (0 : vectr s) = 0 := begin
    admit--intros, ext, exact mul_zero _, exact mul_zero _
end
instance distrib_mul_action_K_vectrK : distrib_mul_action K (vectr s) := ⟨
smul_add_vectr s,
smul_zero_vectr s,
⟩ 

-- renaming vs template due to clash with name "s" for prevailing variable
lemma add_smul_vectr : ∀ (a b : K) (x : vectr s), (a + b) • x = a • x + b • x := 
begin
  intros,
  ext,
  exact right_distrib _ _ _,
  exact right_distrib _ _ _
end

lemma zero_smul_vectr : ∀ (x : vectr s), (0 : K) • x = 0 := begin
    intros,
    ext,
    admit,admit--exact zero_mul _, exact zero_mul _
end
instance module_K_vectrK : module K (vectr s) := ⟨ 
    add_smul_vectr s, 
    zero_smul_vectr s, 
⟩ 

instance add_comm_group_vectr : add_comm_group (vectr s) := 
{
    add_comm := begin
        exact add_comm_vectr s
        
        /-intros,
        ext,
        let h0 : (a + b).coords = a.coords + b.coords := rfl,
        let h1 : (b + a).coords = b.coords + a.coords := rfl,
        rw [h0,h1],
        exact add_comm _ _,
        exact add_comm _ _,-/
    end,
--to_add_group := (show add_group (vec K), by apply_instance),
--to_add_comm_monoid := (show add_comm_monoid (vec K), by apply_instance),
..(show add_group (vectr s), by apply_instance)
}
/-⟨
-- add_group
    add_vectr_vectr s, add_assoc_vectr s, vectr_zero s, zero_add_vectr s, add_zero_vectr s, -- add_monoid
    neg_vectr s,                                                                  -- has_neg
    sub_vectr_vectr s,                                                              -- has_sub
    sub_eq_add_neg_vectr s, 
    add_left_neg_vectr s,
-- commutativity
    add_comm_vectr s,
⟩-/

instance : module K (vectr s) := module_K_vectrK s

/-
    ********************
    *** Affine space ***
    ********************
-/

/-
Affine operations
-/
instance : has_add (vectr s) := ⟨add_vectr_vectr s⟩
instance : has_zero (vectr s) := ⟨vectr_zero s⟩
instance : has_neg (vectr s) := ⟨neg_vectr s⟩

/-
Lemmas needed to implement affine space API
-/
@[simp]
def sub_point_point (p1 p2 : point s) : vectr s := mk_vectr' s (p1.coords -ᵥ p2.coords)
@[simp]
def add_point_vectr (p : point s) (v : vectr s) : point s := 
    mk_point' s (v.coords +ᵥ p.coords) -- reorder assumes order is irrelevant
@[simp]
def add_vectr_point (v : vectr s) (p : point s) : point s := 
    mk_point' s (v.coords +ᵥ p.coords)

@[simp]
def aff_vectr_group_action : vectr s → point s → point s := add_vectr_point s
instance : has_vadd (vectr s) (point s) := ⟨aff_vectr_group_action s⟩

lemma zero_vectr_vadd'_a1 : ∀ p : point s, (0 : vectr s) +ᵥ p = p := begin
    intros,
    ext,--exact zero_add _,
    exact add_zero _,
    --exact add_zero _
    admit
end

lemma vectr_add_assoc'_a1 : ∀ (g1 g2 : vectr s) (p : point s), g1 +ᵥ (g2 +ᵥ p) = g1 + g2 +ᵥ p := begin
    intros, ext,
    repeat {
    have h0 : (g1 +ᵥ (g2 +ᵥ p)).coords = (g1.coords +ᵥ (g2.coords +ᵥ p.coords)) := rfl,
    have h1 : (g1 + g2 +ᵥ p).coords = (g1.coords +ᵥ g2.coords +ᵥ p.coords) := rfl,
    rw [h0,h1],
    simp *,
    simp [has_vadd.vadd, has_add.add, add_semigroup.add, add_zero_class.add,  add_monoid.add, sub_neg_monoid.add, 
        add_group.add, distrib.add, ring.add, division_ring.add],
    cc,
    }
end

instance vectr_add_action: add_action (vectr s) (point s) := 
⟨ 
begin
    exact zero_vectr_vadd'_a1 s
end,
begin
    let h0 := vectr_add_assoc'_a1 s,
    intros,
    exact (h0 g₁ g₂ p).symm
end
⟩

@[simp]
def aff_point_group_sub : point s → point s → vectr s := sub_point_point s
instance point_has_vsub : has_vsub (vectr s) (point s) := ⟨ aff_point_group_sub s ⟩ 

instance : nonempty (point s) := ⟨mk_point s ⟨list.repeat 0 dim,sorry⟩⟩

lemma point_vsub_vadd_a1 : ∀ (p1 p2 : (point s)), (p1 -ᵥ p2) +ᵥ p2 = p1 := begin
    intros, ext,
    --repeat {
    admit,admit
end


lemma point_vadd_vsub_a1 : ∀ (g : vectr s) (p : point s), g +ᵥ p -ᵥ p = g := 
begin
    intros, ext,
    repeat {
    have h0 : ((g +ᵥ p -ᵥ p) : vectr s).coords = (g.coords +ᵥ p.coords -ᵥ p.coords) := rfl,
    rw h0,
    simp *,
    }
end


/-instance aff_point_torsor : add_torsor (vectr s) (point s) := 
⟨ 
    aff_vectr_group_action s,
    zero_vectr_vadd'_a1 s,    -- from add_action
    vectr_add_assoc'_a1 s,    -- from add_action
    aff_point_group_sub s,    -- from has_vsub
    point_vsub_vadd_a1 s,     -- from add_torsor
    point_vadd_vsub_a1 s,     -- from add_torsor
⟩-/

instance : affine_space (vectr s) (point s) := ⟨
    point_vsub_vadd_a1 s,
    point_vadd_vsub_a1 s,
⟩



/-
And now for transforms
-/

--variables {f1 :  fm K dim id_vec} {f2 :  fm K dim id_vec} (s1 : spc K f1) (s2 : spc K f2)
#check (point s) ≃ᵃ[K] (point s)
--not usable?
abbreviation raw_tr := (pt_n K dim) ≃ᵃ[K] (pt_n K dim)
--abbreviation fm_tr := (point s1) ≃ᵃ[K] (point s2)

structure fm_tr 
    {f1 :  fm K dim id_vec} {f2 :  fm K dim id_vec} 
    (s1 : spc K f1) (s2 : spc K f2)  extends (point s1) ≃ᵃ[K] (point s2)


def fm_tr.symm  {f1 :  fm K dim id_vec} {f2 :  fm K dim id_vec} 
    {s1 : spc K f1} {s2 : spc K f2} (ftr : fm_tr s1 s2) : fm_tr s2 s1 :=
    ⟨ftr.1.symm⟩


def fm_tr.trans  {f1 :  fm K dim id_vec} {f2 :  fm K dim id_vec} {f3 :  fm K dim id_vec} 
    {s1 : spc K f1} {s2 : spc K f2} {s3 : spc K f3} (ftr : fm_tr s1 s2) : fm_tr s2 s3 → fm_tr s1 s3 :=
    λftr_, ⟨ftr.1.trans ftr_.1⟩

def basis_to_matrix (ftok : fin dim → pt_n K dim) : matrix (fin dim) (fin dim) K :=
    λ i j,
    ((ftok j) i).coord

def fm.to_homogeneous_matrix (f_ : fm K dim id_vec) : matrix (fin (dim + 1)) (fin (dim + 1)) K
    := 
    λ i j, 
    if i=0 ∧ j=0 then 1 
    else if i=0 then 0
    else if j = 0 then (f_.origin ⟨i.1-1, sorry⟩).coord
    else (f_.basis ⟨j.1-1,sorry⟩ ⟨i.1-1, sorry⟩).coord

def point.to_homogeneous_coords (p : point s) : fin (dim+1) → K
    := 
    λi,
    if i=0 then 1
    else (p.coords ⟨i.1-1, sorry⟩).coord

def vectr.to_homogeneous_coords (v : vectr s) : fin (dim+1) → K
    := 
    λi,
    if i=0 then 0
    else (v.coords ⟨i.1-1, sorry⟩).coord

def mk_point_from_homogeneous_coords (coords_:fin (dim+1) → K) : point s
    := 
    let findim : fin dim → pt K := λi, mk_pt K (coords_ ⟨i.1+1,sorry⟩) in
    mk_point' s findim

def mk_vectr_from_homogeneous_coords (coords_:fin (dim+1) → K) : vectr s
    := 
    let findim : fin dim → vec K := λi, mk_vec K (coords_ ⟨i.1+1,sorry⟩) in
    mk_vectr' s findim

def pt_n.to_homogeneous_coords (p : pt_n K dim) : fin (dim+1) → K
    := 
    λi, if i=0 then 0 
    else (p ⟨i.1-1,sorry⟩).coord

def vec_n.to_homogeneous_coords (v : vec_n K dim) : fin (dim+1) → K
    :=
    λi, if i=0 then 0 
    else (v ⟨i.1-1,sorry⟩).coord

def mk_pt_n_from_homogeneous_coords (coords_:fin (dim+1) → K) : pt_n K dim
    := 
    λi, mk_pt K (coords_ ⟨i.1+1,sorry⟩)

def mk_vec_n_from_homogeneous_coords (coords_:fin (dim+1) → K) : vec_n K dim
    :=
    λi, mk_vec K (coords_ ⟨i.1+1,sorry⟩)


#check f.to_homogeneous_matrix
/-
TODO: This material needs inspection, verification
-/
/-
equation compiler failed to generate bytecode for 'to_base_helper'._main'
nested exception message:
code generation failed, VM does not have code for 'classical.choice'
-/
/-
stuck at noncomputable for now
-/
/-
noncomputable def to_base_helper' :  fm K dim id_vec → @raw_tr K _ _ dim
| (fm.base dim id_vec) := ⟨
            ⟨   /-base case -/
                (λ p, p),
                (λ p, p),
                begin
                    unfold function.left_inverse,
                    intros,
                    simp *
                end,
                begin
                    unfold function.right_inverse function.left_inverse,
                    intros,
                    simp *
                end
            ⟩,
            ⟨
                (λ v, v),
                begin
                    intros, simp*
                end,
               -- (λ v, ⟨v.coords⟩),
                begin
                    intros, simp *
                end,
                (λ v, v),
                begin
                    unfold function.left_inverse,
                    intros, simp *
                end,
                begin
                    unfold function.left_inverse function.right_inverse,
                    intros, simp *
                end,
            ⟩,
            begin
                simp *,
                --admit   -- TODO: What's this?
            end
        ⟩
| (fm.deriv origin basis parent) := (⟨
            ⟨/-transform from current->parent-/
                (λ (p : pt_n K dim),
                mk_pt_n_from_homogeneous_coords 
                (((fm.deriv origin basis parent).to_homogeneous_matrix.mul_vec p.to_homogeneous_coords) : fin (dim + 1) → K)
                : pt_n K dim → pt_n K dim),
                (λ (p : pt_n K dim),
                mk_pt_n_from_homogeneous_coords 
                ((((fm.deriv origin basis parent).to_homogeneous_matrix.nonsing_inv).mul_vec p.to_homogeneous_coords) : fin (dim + 1) → K)
                : pt_n K dim → pt_n K dim),
                sorry,
                sorry,
            ⟩,
            ⟨
                λv, v,
                sorry,
                sorry,
                sorry,
                sorry,
                sorry
            ⟩,
            sorry /-invert to parent->current and append to current->base-/
⟩ : @raw_tr K _ _ dim).trans (to_base_helper' parent)
| (fm.prod f1 f2 prod_origin prod_basis) := ⟨
            ⟨/-transform from current->parent-/
                (λ (p : pt_n K dim),
                mk_pt_n_from_homogeneous_coords 
                (((fm.prod f1 f2 prod_origin prod_basis).to_homogeneous_matrix.mul_vec p.to_homogeneous_coords) : fin (dim + 1) → K)
                : pt_n K dim → pt_n K dim),
                (λ (p : pt_n K dim),
                mk_pt_n_from_homogeneous_coords 
                ((((fm.prod f1 f2 prod_origin prod_basis).to_homogeneous_matrix.nonsing_inv).mul_vec p.to_homogeneous_coords) : fin (dim + 1) → K)
                : pt_n K dim → pt_n K dim),
                sorry,
                sorry,
            ⟩,
            ⟨
                λv, v,
                sorry,
                sorry,
                sorry,
                sorry,
                sorry
            ⟩,
            sorry /-invert to parent->current and append to current->base-/
⟩
-/
noncomputable def to_base_helper' :  fm K dim id_vec → @raw_tr K _ _ dim :=
begin
    intros f,
    cases f,
    { exact ⟨
            ⟨   /-base case -/
                (λ p, p),
                (λ p, p),
                begin
                    unfold function.left_inverse,
                    intros,
                    simp *
                end,
                begin
                    unfold function.right_inverse function.left_inverse,
                    intros,
                    simp *
                end
            ⟩,
            ⟨
                (λ v, v),
                begin
                    intros, simp*
                end,
               -- (λ v, ⟨v.coords⟩),
                begin
                    intros, simp *
                end,
                (λ v, v),
                begin
                    unfold function.left_inverse,
                    intros, simp *
                end,
                begin
                    unfold function.left_inverse function.right_inverse,
                    intros, simp *
                end,
            ⟩,
            begin
                simp *,
                --admit   -- TODO: What's this?
            end
        ⟩},
    { exact (⟨
            ⟨/-transform from current->parent-/
                (λ (p : pt_n K dim),
                mk_pt_n_from_homogeneous_coords 
                (((fm.deriv f_origin f_basis f_parent).to_homogeneous_matrix.mul_vec p.to_homogeneous_coords) : fin (dim + 1) → K)
                : pt_n K dim → pt_n K dim),
                (λ (p : pt_n K dim),
                mk_pt_n_from_homogeneous_coords 
                ((((fm.deriv f_origin f_basis f_parent).to_homogeneous_matrix.nonsing_inv).mul_vec p.to_homogeneous_coords) : fin (dim + 1) → K)
                : pt_n K dim → pt_n K dim),
                sorry,
                sorry,
            ⟩,
            ⟨
                λv, v,
                sorry,
                sorry,
                sorry,
                sorry,
                sorry
            ⟩,
            sorry /-invert to parent->current and append to current->base-/
⟩ : @raw_tr K _ _ dim).trans (to_base_helper' f_parent)
    },
    {
        exact ⟨
            ⟨/-transform from current->parent-/
                (λ (p : pt_n K dim),
                mk_pt_n_from_homogeneous_coords 
                (((fm.prod f1 f2 prod_origin prod_basis).to_homogeneous_matrix.mul_vec p.to_homogeneous_coords) : fin (dim + 1) → K)
                : pt_n K dim → pt_n K dim),
                (λ (p : pt_n K dim),
                mk_pt_n_from_homogeneous_coords 
                ((((fm.prod f1 f2 prod_origin prod_basis).to_homogeneous_matrix.nonsing_inv).mul_vec p.to_homogeneous_coords) : fin (dim + 1) → K)
                : pt_n K dim → pt_n K dim),
                sorry,
                sorry,
            ⟩,
            ⟨
                λv, v,
                sorry,
                sorry,
                sorry,
                sorry,
                sorry
            ⟩,
            sorry /-invert to parent->current and append to current->base-/
⟩
    }
end
/-
| (fm.base dim id_vec) := ⟨
            ⟨   /-base case -/
                (λ p, p),
                (λ p, p),
                begin
                    unfold function.left_inverse,
                    intros,
                    simp *
                end,
                begin
                    unfold function.right_inverse function.left_inverse,
                    intros,
                    simp *
                end
            ⟩,
            ⟨
                (λ v, v),
                begin
                    intros, simp*
                end,
               -- (λ v, ⟨v.coords⟩),
                begin
                    intros, simp *
                end,
                (λ v, v),
                begin
                    unfold function.left_inverse,
                    intros, simp *
                end,
                begin
                    unfold function.left_inverse function.right_inverse,
                    intros, simp *
                end,
            ⟩,
            begin
                simp *,
                --admit   -- TODO: What's this?
            end
        ⟩
| (fm.deriv origin basis parent) := (⟨
            ⟨/-transform from current->parent-/
                (λ (p : pt_n K dim),
                mk_pt_n_from_homogeneous_coords 
                (((fm.deriv origin basis parent).to_homogeneous_matrix.mul_vec p.to_homogeneous_coords) : fin (dim + 1) → K)
                : pt_n K dim → pt_n K dim),
                (λ (p : pt_n K dim),
                mk_pt_n_from_homogeneous_coords 
                ((((fm.deriv origin basis parent).to_homogeneous_matrix.nonsing_inv).mul_vec p.to_homogeneous_coords) : fin (dim + 1) → K)
                : pt_n K dim → pt_n K dim),
                sorry,
                sorry,
            ⟩,
            ⟨
                λv, v,
                sorry,
                sorry,
                sorry,
                sorry,
                sorry
            ⟩,
            sorry /-invert to parent->current and append to current->base-/
⟩ : @raw_tr K _ _ dim).trans (to_base_helper' parent)
| (fm.prod f1 f2 prod_origin prod_basis) := ⟨
            ⟨/-transform from current->parent-/
                (λ (p : pt_n K dim),
                mk_pt_n_from_homogeneous_coords 
                (((fm.prod f1 f2 prod_origin prod_basis).to_homogeneous_matrix.mul_vec p.to_homogeneous_coords) : fin (dim + 1) → K)
                : pt_n K dim → pt_n K dim),
                (λ (p : pt_n K dim),
                mk_pt_n_from_homogeneous_coords 
                ((((fm.prod f1 f2 prod_origin prod_basis).to_homogeneous_matrix.nonsing_inv).mul_vec p.to_homogeneous_coords) : fin (dim + 1) → K)
                : pt_n K dim → pt_n K dim),
                sorry,
                sorry,
            ⟩,
            ⟨
                λv, v,
                sorry,
                sorry,
                sorry,
                sorry,
                sorry
            ⟩,
            sorry /-invert to parent->current and append to current->base-/
⟩
-/

#check linear_equiv.mk
#reduce pt_n K dim ≃ pt_n K dim
 
noncomputable def spc.to_base {f1 :  fm K dim id_vec} (s1 : spc K f1) : @raw_tr K _ _ dim := to_base_helper' f1

noncomputable def spc.fm_tr {f1 :  fm K dim id_vec} {f2 :  fm K dim id_vec} (s1 : spc K f1) : Π (s2 : spc K f2),
    fm_tr s1 s2 
    := 
     --(point s1) ≃ᵃ[K] (point s2) := 
    λ s2,
    ⟨
    let rawtr : @raw_tr K _ _ dim := s1.to_base.trans s2.to_base.symm in
                ⟨
            ⟨
                (λ p : point _, (⟨(rawtr p.1 : pt_n K dim)⟩ : point _)),
                (λ p : point _, (⟨(rawtr p.1 : pt_n K dim)⟩ : point _)),
                sorry,
                sorry
            ⟩,
            ⟨
                (λv : vectr _, (⟨(rawtr.linear v.1 : vec_n K dim)⟩ : vectr _)),
                sorry,
               -- (λ v, ⟨v.coords⟩),
                sorry,
                (λv : vectr _, (⟨(rawtr.linear v.1 : vec_n K dim)⟩ : vectr _)),
                sorry,
                sorry
            ⟩,
            sorry
        ⟩
    ⟩

def fm_tr.transform_point  
    {f1 :  fm K dim id_vec} {f2 :  fm K dim id_vec} 
    {s1 : spc K f1} {s2 : spc K f2} (tr:fm_tr s1 s2 ) 
    : point s1 → point s2 :=
    λp,
    tr.to_equiv p

def fm_tr.transform_vectr  
    {f1 :  fm K dim id_vec} {f2 :  fm K dim id_vec} 
    {s1 : spc K f1} {s2 : spc K f2} (tr:fm_tr s1 s2 ) 
    : vectr s1 → vectr s2 :=
    λv,
    let as_pt : point s1 := (⟨⟨(1,v.coords.to_prod.2),rfl⟩⟩) in
    let tr_pt := (tr.to_equiv as_pt) in
    ⟨⟨(0, tr_pt.coords.to_prod.2),rfl⟩⟩


/-
DEMO: transform generation between arbitrary affine coordinate spaces on physical dimension
-/
variables {f1 :  fm K dim id_vec} {f2 :  fm K dim id_vec} (s1 : spc K f1) (s2 : spc K f2)

def s1_to_s2 : _ := s1.fm_tr s2     -- Yay!

#check s1_to_s2 s1 s2

variables (my_vec : vectr s1)

#check ((s1_to_s2 s1 s2).transform_vectr) (((s1_to_s2 s1 s2).transform_vectr) my_vec)

end implicitK

-- TODO: clean up naming in this file