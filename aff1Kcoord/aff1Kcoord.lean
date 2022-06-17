import .aff1K
import category_theory.groupoid
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

/-
Is this where we root distinctions between affine spaces for different dimensionss?
-/
inductive fm : nat → Type u
| base : Π n, fm n
| deriv : Π n, (prod (pt K) (vec K)) → fm n → fm n  -- TODO: curry all of these args

/-
inductive fm : nat → Type u
| base : ∀ (n : nat), fm n
| deriv : ∀ (n : nat), (prod (pt K) (vec K)) → fm n → fm n
-/

def mk_fm  {n : nat } (p : pt K) (v : vec K) (f : fm K n): fm K n := fm.deriv n (p, v) f 

structure spc {n : nat} (f : fm K n) : Type u       -- interesting specimen, here, btw

def mk_space {n : nat} (f : fm K n) :=
  @spc.mk K _ _ n f 

end explicitK

section implicitK

variables 
{K : Type u} [field K] [inhabited K] 
{n : nat} {f : fm K n} (s : spc K f)

/-
Augment pt and vec types with spaces and frames and
then make operations apply only for objects in same
space (and thus frame).
-/
@[ext]
structure point {f : fm K n} (s : @spc K _ _ n f ) extends pt K
@[simp]
def mk_point' (p : pt K) : point s := point.mk p  
@[simp]
def mk_point (k : K) : point s := point.mk (mk_pt K k)  

def p := mk_point s (3:K)

@[ext]
structure vectr {f : fm K n} (s : spc K f ) extends vec K
@[simp]
def mk_vectr' (v : vec K) : vectr s := vectr.mk v
@[simp]
def mk_vectr (k : K) : vectr s := vectr.mk (mk_vec K k)  

-- note that we don't extend fm
def mk_frame {parent : fm K n} {s : spc K parent}  (p : point s) (v : vectr s) :=
fm.deriv n (p.to_pt, v.to_vec) parent   -- TODO: make sure v ≠ 0 (erasing tyoe info)
                                      -- TODO: snd arg is really a basis for the vs


/-
    *************************************
    Instantiate module K (vector K)
    *************************************
-/

variables v1 v2 : @vectr K _ _ n f s
#check v1.to_vec
#check v2.to_vec + v1.to_vec

@[simp]
def add_vectr_vectr (v1 v2 : vectr s) : vectr s :=  mk_vectr' s (v1.to_vec + v2.to_vec)
@[simp]
def smul_vectr (k : K) (v : vectr s) : vectr s := mk_vectr' s (k • v.to_vec)
@[simp]
def neg_vectr (v : vectr s) : vectr s := mk_vectr' s ((-1 : K) • v.to_vec)
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
    have p1 : (a + b + c).to_vec = a.to_vec + b.to_vec + c.to_vec := rfl,
    have p2 : (a + (b + c)).to_vec = a.to_vec + (b.to_vec + c.to_vec) := rfl,
    rw [p1,p2],
    cc
    }
end


instance add_semigroup_vectr : add_semigroup (vectr s) := ⟨ add_vectr_vectr s, add_assoc_vectr s⟩ 

@[simp]
def vectr_zero := @mk_vectr K _ _ n f s (0:K)
instance has_zero_vectr : has_zero (vectr s) := ⟨vectr_zero s⟩

#check mul_zero_class.zero

lemma zero_add_vectr : ∀ a : vectr s, 0 + a = a := 
begin
    intros,--ext,
    ext,
    let h0 : (0 + a).to_vec = (0 : vectr s).to_vec + a.to_vec := rfl,
    simp [h0],
    exact zero_add _,
end

lemma add_zero_vectr : ∀ a : vectr s, a + 0 = a := 
begin
    intros,ext,
    exact add_zero _,
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
    refl,

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
    ext,
    have h0 : (-a + a).to_vec = -a.to_vec + a.to_vec := begin
        have h₁ : -a + a = add_vectr_vectr _ (-a) a := rfl,
        rw h₁,
        dsimp only [add_vectr_vectr],
        dsimp only [mk_vectr'],
        have h₂ : -a = neg_vectr _ a := rfl,
        rw h₂,
        dsimp only [neg_vectr, mk_vectr'],
        suffices h : (-(1 : K)) • a.to_vec = -a.to_vec,
        rw h,
        simp only [one_smul, neg_smul],
    end,
    simp [h0],
    have : (0:vec K) = (0:vectr s).to_vec := rfl,
    simp *,
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
    have p1 : (a + b).to_vec = a.to_vec + b.to_vec:= rfl,
    have p2 : (b + a).to_vec = b.to_vec + a.to_vec := rfl,
    rw [p1,p2],
    cc
    }    
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
        have h0 : ((1:K) • b).to_vec = ((1:K)•(b.to_vec)) := rfl,
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
end

instance mul_action_vectr : mul_action K (vectr s) := ⟨
one_smul_vectr s,
mul_smul_vectr s,
⟩ 

lemma smul_add_vectr : ∀(r : K) (x y : vectr s), r • (x + y) = r • x + r • y := begin
    intros, ext,
    repeat {
    have h0 : (r • (x + y)).to_vec = (r • (x.to_vec + y.to_vec)) := rfl,
    have h1 : (r•x + r•y).to_vec = (r•x.to_vec + r•y.to_vec) := rfl,
    rw [h0,h1],
    simp *,
    }

end

lemma smul_zero_vectr : ∀(r : K), r • (0 : vectr s) = 0 := begin
    intros, ext, exact mul_zero _
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
  exact right_distrib _ _ _
end

lemma zero_smul_vectr : ∀ (x : vectr s), (0 : K) • x = 0 := begin
    intros,
    ext,
    exact zero_mul _,
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
        let h0 : (a + b).to_vec = a.to_vec + b.to_vec := rfl,
        let h1 : (b + a).to_vec = b.to_vec + a.to_vec := rfl,
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
def sub_point_point (p1 p2 : point s) : vectr s := mk_vectr' s (p1.to_pt -ᵥ p2.to_pt)
@[simp]
def add_point_vectr {f : fm K n} {s : spc K f } (p : point s) (v : vectr s) : point s := 
    mk_point' s (v.to_vec +ᵥ p.to_pt) -- reorder assumes order is irrelevant
@[simp]
def add_vectr_point {f : fm K n} {s : spc K f } (v : vectr s) (p : point s) : point s := 
    mk_point' s (v.to_vec +ᵥ p.to_pt)

@[simp]
def aff_vectr_group_action : vectr s → point s → point s := add_vectr_point
instance : has_vadd (vectr s) (point s) := ⟨aff_vectr_group_action s⟩

lemma zero_vectr_vadd'_a1 : ∀ p : point s, (0 : vectr s) +ᵥ p = p := begin
    intros,
    ext,--exact zero_add _,
    exact add_zero _
end

lemma vectr_add_assoc'_a1 : ∀ (g1 g2 : vectr s) (p : point s), g1 +ᵥ (g2 +ᵥ p) = g1 + g2 +ᵥ p := begin
    intros, ext,
    repeat {
    have h0 : (g1 +ᵥ (g2 +ᵥ p)).to_pt = (g1.to_vec +ᵥ (g2.to_vec +ᵥ p.to_pt)) := rfl,
    have h1 : (g1 + g2 +ᵥ p).to_pt = (g1.to_vec +ᵥ g2.to_vec +ᵥ p.to_pt) := rfl,
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

instance : nonempty (point s) := ⟨mk_point s 0⟩

lemma point_vsub_vadd_a1 : ∀ (p1 p2 : (point s)), (p1 -ᵥ p2) +ᵥ p2 = p1 := begin
    intros, ext,
    --repeat {
    have h0 : (p1 -ᵥ p2 +ᵥ p2).to_pt = (p1.to_pt -ᵥ p2.to_pt +ᵥ p2.to_pt) := rfl,
    rw h0,
    simp [has_vsub.vsub, has_sub.sub, sub_neg_monoid.sub, add_group.sub, add_comm_group.sub, ring.sub, division_ring.sub],
    simp [has_vadd.vadd, has_add.add, distrib.add, ring.add, division_ring.add],
    let h0 : field.add p2.to_pt.to_prod.fst (field.sub p1.to_pt.to_prod.fst p2.to_pt.to_prod.fst) = 
            field.add (field.sub p1.to_pt.to_prod.fst p2.to_pt.to_prod.fst) p2.to_pt.to_prod.fst := add_comm _ _,
    rw h0,
    exact sub_add_cancel _ _,
    have h0 : (p1 -ᵥ p2 +ᵥ p2).to_pt = (p1.to_pt -ᵥ p2.to_pt +ᵥ p2.to_pt) := rfl,
    rw h0,
    simp [has_vsub.vsub, has_sub.sub, sub_neg_monoid.sub, add_group.sub, add_comm_group.sub, ring.sub, division_ring.sub],
    simp [has_vadd.vadd, has_add.add, distrib.add, ring.add, division_ring.add],
    let h0 : field.add p2.to_pt.to_prod.snd (field.sub p1.to_pt.to_prod.snd p2.to_pt.to_prod.snd) = 
            field.add (field.sub p1.to_pt.to_prod.snd p2.to_pt.to_prod.snd) p2.to_pt.to_prod.snd := add_comm _ _,
    rw h0,
    exact sub_add_cancel _ _,
    --have h1 : (p1.to_pt -ᵥ p2.to_pt +ᵥ p2.to_pt).to_prod = (p1.to_pt.to_prod -ᵥ p2.to_pt.to_prod +ᵥ p2.to_pt.to_prod) := by simp *,
    
    --}
end


lemma point_vadd_vsub_a1 : ∀ (g : vectr s) (p : point s), g +ᵥ p -ᵥ p = g := 
begin
    intros, ext,
    repeat {
    have h0 : ((g +ᵥ p -ᵥ p) : vectr s).to_vec = (g.to_vec +ᵥ p.to_pt -ᵥ p.to_pt) := rfl,
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
    begin
        exact point_vsub_vadd_a1 s,
    end,
    begin
        exact point_vadd_vsub_a1 s,
    end,

⟩



/-
And now for transforms
-/

--variables {f1 : fm K n} {f2 : fm K n} (s1 : spc K f1) (s2 : spc K f2)
#check (point s) ≃ᵃ[K] (point s)
--not usable?
abbreviation raw_tr := (pt K) ≃ᵃ[K] (pt K)
--abbreviation fm_tr := (point s1) ≃ᵃ[K] (point s2)

@[ext]
structure fm_tr {f1 : fm K n} {f2 : fm K n} (s1 : spc K f1) (s2 : spc K f2)  extends (point s1) ≃ᵃ[K] (point s2)

def fm_tr.refl {f1 : fm K n} (s1 : spc K f1) : fm_tr s1 s1 :=
    ⟨⟨
        equiv.refl (point s1),
        linear_equiv.refl K (vectr s1),
        λ _ _, rfl
    ⟩⟩

def fm_tr.symm  {f1 : fm K n} {f2 : fm K n} {s1 : spc K f1} {s2 : spc K f2} (ftr : fm_tr s1 s2) : fm_tr s2 s1 :=
    ⟨ftr.1.symm⟩


def fm_tr.trans  {f1 : fm K n} {f2 : fm K n} {f3 : fm K n} {s1 : spc K f1} {s2 : spc K f2} {s3 : spc K f3} (ftr : fm_tr s1 s2) : fm_tr s2 s3 → fm_tr s1 s3 :=
    λftr_, ⟨ftr.1.trans ftr_.1⟩


#check (fin 2)
/-
inductive fm : nat → Type u
| base : Π n, fm n
| deriv : Π n, (prod (pt K) (vec K)) → fm n → fm n 
-/
/-
@[simp]
def fm.to_coords_matrix (f : fm K n) : matrix (fin 2) (fin 2) K
    := 
    match f with 
    | (fm.base n) := λ i j, 
        if i = 0 ∧ j = 0 then 1 else 
        (if i = 0 ∧ j = 1 then 0 else (
            if i = 1 ∧ j = 0 then 0 else
                (if i = 1 ∧ j = 1 then 1 else 0)
        ))
    | (fm.deriv n c parent) := λ i j,
        if i = 0 ∧ j = 0 then c. else 
        (if i = 0 ∧ j = 1 then 0 else (
            if i = 1 ∧ j = 0 then 0 else
                (if i = 1 ∧ j = 1 then 1 else 0)
        ))
    end
-/



/-
TODO: This material needs inspection, verification
-/
#check @function.left_inverse
def to_base_helper' : fm K n → @raw_tr K _ _
| (fm.base n) := ⟨
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
               -- (λ v, ⟨v.to_vec⟩),
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
| (fm.deriv n c parent) := (⟨
            ⟨/-transform from current->parent-/
                λp, ⟨(1, 
                        p.to_prod.2*c.snd.to_prod.2 + c.fst.to_prod.2),
                        begin
                            cases p,
                            
                        end⟩,
                    λp, (⟨(1, 
                        (p.to_prod.2 - c.fst.to_prod.2 )/c.snd.to_prod.2),sorry⟩),
                sorry,
                sorry
            ⟩,
            ⟨
                λv, ⟨(0, v.to_prod.2*c.snd.to_prod.2),begin 
                    cases v,
                    simp *,
                end⟩,
                sorry,
                sorry,
                λv, ⟨(0, v.to_prod.2/c.snd.to_prod.2),begin 
                    cases v,
                    simp *,
                end⟩,
                sorry,
                sorry
            ⟩,
            sorry /-invert to parent->current and append to current->base-/
        ⟩ : @raw_tr K _ _).trans (to_base_helper' parent)

 
def spc.to_base {f1 : fm K n} (s1 : spc K f1) : @raw_tr K _ _ := to_base_helper' f1

def spc.fm_tr {f1 : fm K n} {f2 : fm K n} (s1 : spc K f1) : Π (s2 : spc K f2),
    fm_tr s1 s2 
    := 
     --(point s1) ≃ᵃ[K] (point s2) := 
    λ s2,
    ⟨
    let rawtr : @raw_tr K _ _ := s1.to_base.trans s2.to_base.symm in
                ⟨
            ⟨
                (λ p : point _, (⟨(rawtr p.1 : pt K)⟩ : point _)),
                (λ p : point _, (⟨(rawtr p.1 : pt K)⟩ : point _)),
                sorry,
                sorry
            ⟩,
            ⟨
                (λv : vectr _, (⟨(rawtr.linear v.1 : vec K)⟩ : vectr _)),
                sorry,
               -- (λ v, ⟨v.to_vec⟩),
                sorry,
                (λv : vectr _, (⟨(rawtr.linear v.1 : vec K)⟩ : vectr _)),
                sorry,
                sorry
            ⟩,
            sorry
        ⟩
    ⟩

def fm_tr.transform_point  {f1 : fm K n} {f2 : fm K n} {s1 : spc K f1} {s2 : spc K f2} (tr:fm_tr s1 s2 ) : point s1 → point s2 :=
    λp,
    tr.to_equiv p

def fm_tr.transform_vectr  {f1 : fm K n} {f2 : fm K n} {s1 : spc K f1} {s2 : spc K f2} (tr:fm_tr s1 s2 ) : vectr s1 → vectr s2 :=
    λv,
    let as_pt : point s1 := (⟨⟨(1,v.to_vec.to_prod.2),rfl⟩⟩) in
    let tr_pt := (tr.to_equiv as_pt) in
    ⟨⟨(0, tr_pt.to_pt.to_prod.2),rfl⟩⟩


/-
DEMO: transform generation between arbitrary affine coordinate spaces on physical dimension
-/
variables {f1 : fm K n} {f2 : fm K n} (s1 : spc K f1) (s2 : spc K f2)

def s1_to_s2 : _ := s1.fm_tr s2     -- Yay!

#check s1_to_s2 s1 s2

variables (my_vec : vectr s1)

#check ((s1_to_s2 s1 s2).transform_vectr) (((s1_to_s2 s1 s2).transform_vectr) my_vec)

instance : quiver (spc K f) := ⟨λ (s1 s2 : spc K f), fm_tr s1 s2⟩

instance : category_theory.category_struct (spc K f) := ⟨
    λ (s : spc K f), fm_tr.refl s, -- identity transformation
    λ {s1 s2 s3 : spc K f} (f : fm_tr s1 s2) (g : fm_tr s2 s3), fm_tr.trans f g -- f ∘ g
⟩

instance : category_theory.category (spc K f) := ⟨
    begin
        simp only [auto_param_eq],
        intros,
        have h_orig := (fm_tr.ext_iff (𝟙 X ≫ f_1) f_1).2,
        apply h_orig,
        cases f_1 with f_aff,
        cases f_aff with f_equiv f_linear f_map_vadd',
        dsimp only [category_theory.category_struct.id, fm_tr.refl],
        dsimp only [category_theory.category_struct.comp, fm_tr.trans, affine_equiv.trans],
        ext,
        dsimp only [coe_fn, has_coe_to_fun.coe],
        simp only [equiv.refl_trans],
    end,
    begin
        simp only [auto_param_eq],
        intros,
        have h₀ := (fm_tr.ext_iff (𝟙 X ≫ f_1) f_1).2,
        apply h₀,
        cases f_1 with f_aff,
        cases f_aff with f_equiv f_linear f_map_vadd',
        dsimp only [category_theory.category_struct.id, fm_tr.refl],
        dsimp only [category_theory.category_struct.comp, fm_tr.trans, affine_equiv.trans],
        ext,
        dsimp only [coe_fn, has_coe_to_fun.coe],
        simp only [equiv.refl_trans],
    end,
    begin
        simp only [auto_param_eq],
        intros,
        have h₀ := (fm_tr.ext_iff ((f_1 ≫ g) ≫ h) (f_1 ≫ g ≫ h)).2,
        apply h₀,
        cases f_1 with f_aff,
        cases g with g_aff,
        cases h with h_aff,
        cases f_aff with f_equiv f_linear f_map_vadd',
        cases g_aff with g_equiv g_linear g_map_vadd',
        cases h_aff with h_equiv h_linear h_map_vadd',
        dsimp only [category_theory.category_struct.comp, fm_tr.trans, affine_equiv.trans],
        ext,
        dsimp only [coe_fn, has_coe_to_fun.coe],
        simp only [equiv.trans_assoc],
    end
⟩ 

instance : category_theory.groupoid (spc K f) := ⟨
    λ {s1 s2 : spc K f} (f_1 : fm_tr s1 s2), fm_tr.symm f_1,
    begin
        simp only [auto_param_eq],
        intros,
        dsimp only [category_theory.category_struct.comp],
        have h₀ := (fm_tr.ext_iff ((fm_tr.symm f_1).trans f_1) (𝟙 Y)).2,
        apply h₀,
        dsimp only [category_theory.category_struct.id, fm_tr.refl],
        dsimp only [fm_tr.trans, affine_equiv.trans],
        dsimp only [fm_tr.symm, affine_equiv.symm],
        ext,
        dsimp only [coe_fn, has_coe_to_fun.coe],
        simp only [affine_equiv.coe_to_equiv, equiv.to_fun_as_coe, id.def, function.comp_app, affine_equiv.apply_symm_apply,
            equiv.coe_trans, affine_equiv.symm_to_equiv, equiv.coe_refl],
    end,
    begin
        simp only [auto_param_eq],
        intros,
        dsimp only [category_theory.category_struct.comp],
        have h₀ := (fm_tr.ext_iff (fm_tr.trans f_1 (fm_tr.symm f_1)) (𝟙 X)).2,
        apply h₀,
        dsimp only [category_theory.category_struct.id, fm_tr.refl],
        dsimp only [fm_tr.trans, affine_equiv.trans],
        dsimp only [fm_tr.symm, affine_equiv.symm],
        ext,
        dsimp only [coe_fn, has_coe_to_fun.coe],
        simp only [affine_equiv.coe_to_equiv, equiv.to_fun_as_coe, id.def, function.comp_app, affine_equiv.symm_apply_apply,
            equiv.coe_trans, affine_equiv.symm_to_equiv, equiv.coe_refl],
    end
⟩ 

end implicitK

-- TODO: clean up naming in this file