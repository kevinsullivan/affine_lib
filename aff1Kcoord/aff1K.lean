--import linear_algebra.affine_space.basic
import ..lin2Kcoord.lin2kcoord
import linear_algebra.affine_space.affine_equiv
import tactic.linarith
import algebra.direct_sum
import linear_algebra.direct_sum_module
import tactic.linarith

open_locale direct_sum


universes u 
variables 
(K : Type u) 
[field K]
[inhabited K]

/-
Export affine_space (vec K) (pt K) := aff_pt_torsor K,
with vector_space K (vec K) = semimodule K (vec K).
-/


/-
Objects
-/

-- 1-D *affine* K pt and vec objects rep'd by 2-D linear K tuples
@[ext]
structure pt extends K × K := (inv : fst = 1)
@[simp]
def mk_pt' (p : K × K) (i : p.1 = 1): pt K := @pt.mk K _ _ p i    -- private
@[simp]
def mk_pt (k : K) : pt K  := @pt.mk K _ _ (1, k) rfl              -- exported

def pt.coord {K : Type u} 
[field K]
[inhabited K] (p : pt K) : K := p.to_prod.2

#check K × K
#check prod

@[ext]
structure vec extends K × K := (inv : fst = 0)
@[simp]
def mk_vec' (p : K × K) (i : p.1 = 0): vec K := @vec.mk K _ _ p i -- private
@[simp]
def mk_vec (k : K) : vec K := @vec.mk K _ _ (0, k) rfl            -- exported

def vec.coord {K : Type u} 
[field K]
[inhabited K]  (v : vec K) : K := v.to_prod.2

/-
    ********************
    *** Vector space ***
    ********************
-/


@[simp]
def add_vec_vec (v1 v2 : vec K) : vec K := mk_vec' K (v1.to_prod + v2.to_prod) begin 
    cases v1,
    cases v2,
    simp *,
end

@[simp]
def smul_vec (k : K) (v : vec K) : vec K := mk_vec' K (k • v.to_prod) begin 
    cases v,
    simp *,
end --smul

@[simp]
def neg_vec (v : vec K) : vec K := mk_vec' K ((-1 : K) • v.to_prod) begin 
    cases v,
    simp *,
end --smul
@[simp]
def sub_vec_vec (v2 v1 : vec K) : vec K := add_vec_vec K v2 (neg_vec K v1)  -- v2-v1

/-
class add_semigroup (G : Type u) extends has_add G :=
(add_assoc : ∀ a b c : G, a + b + c = a + (b + c))
-/

/-
has_zero vec
-/
@[simp]
def vec_zero  := mk_vec K 0
instance has_zero_vec : has_zero (vec K) := ⟨vec_zero K⟩

/-
class add_monoid (M : Type u) extends add_semigroup M, has_zero M :=
(zero_add : ∀ a : M, 0 + a = a) (add_zero : ∀ a : M, a + 0 = a)
-/






/-
sub_neg_monoid (G : Type u) extends add_monoid G, has_neg G, has_sub G :=
(sub := λ a b, a + -b)
(sub_eq_add_neg : ∀ a b : G, a - b = a + -b . try_refl_tac)
-/




/-
class add_group (A : Type u) extends sub_neg_monoid A :=
(add_left_neg : ∀ a : A, -a + a = 0)
-/


/-
Material up to now is needed for affine_space, as defined below. 
The rest of this section is needed for vector_space (vec K).
-/

/-
/-- An additive commutative monoid is an additive monoid with commutative `(+)`. -/
@[protect_proj, ancestor add_monoid add_comm_semigroup]
class add_comm_monoid (M : Type u) extends add_monoid M, add_comm_semigroup M
attribute [to_additive] comm_monoid
-/



/-
/-- Typeclass for types with a scalar multiplication operation, denoted `•` (`\bu`) -/
class has_scalar (α : Type u) (γ : Type v) := (smul : α → γ → γ)
-/
--instance has_scalar_vec : has_scalar K (vec K) := sorry
/-⟨
smul_vec K,
⟩-/

/-
/-- Typeclass for multiplicative actions by monoids. This generalizes group actions. -/
@[protect_proj] class mul_action (α : Type u) (β : Type v) [monoid α] extends has_scalar α β :=
(one_smul : ∀ b : β, (1 : α) • b = b)
(mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b)
-/




/-
    ********************
    *** Affine space ***
    ********************
-/

/-
1-D Affine space operations
-/
-- ANDREW TO DR. SULLIVAN : I HAD TO CHANGE THIS DEFINITION FROM p2 - p1 TO p1 - p2
@[simp]
def sub_pt_pt (p1 p2 : pt K) : vec K := mk_vec' K (p1.to_prod - p2.to_prod) begin 
    cases p1, cases p2,

    simp *,
end
@[simp]
def add_pt_vec (p : pt K) (v : vec K) : pt K := mk_pt' K (p.to_prod + v.to_prod) begin
    cases p,
    cases v,
    simp *
end
@[simp]
def add_vec_pt (v : vec K) (p : pt K) : pt K := mk_pt' K (p.to_prod + v.to_prod) begin
    cases v,
    cases p,
    simp *
end
-- add affine combination operation here 



/-
has_vadd (vector point addition)
-/
@[simp]
def aff_vec_group_action : vec K → pt K → pt K := add_vec_pt K
instance : has_vadd (vec K) (pt K) := ⟨aff_vec_group_action K⟩


/-
class has_vsub (G : out_param Type*) (P : Type*) :=
(vsub : P → P → G)
-/
@[simp]
def aff_pt_group_sub : pt K → pt K → vec K := sub_pt_pt K
instance pt_has_vsub : has_vsub (vec K) (pt K) := ⟨ aff_pt_group_sub K ⟩ 

/-
/-- An `add_torsor G P` gives a structure to the nonempty type `P`,
acted on by an `add_group G` with a transitive and free action given
by the `+ᵥ` operation and a corresponding subtraction given by the
`-ᵥ` operation. In the case of a vector space, it is an affine
space. -/
class add_torsor (G : out_param Type*) (P : Type*) [out_param $ add_group G]
  extends add_action G P, has_vsub G P :=
[nonempty : nonempty P]
(vsub_vadd' : ∀ (p1 p2 : P), (p1 -ᵥ p2 : G) +ᵥ p2 = p1)
(vadd_vsub' : ∀ (g : G) (p : P), g +ᵥ p -ᵥ p = g)
-/

/-
Affine 1 K space
-/
open_locale affine

instance : has_neg (vec K) := ⟨neg_vec K⟩

@[simp]
def nsmul_vec : ℕ → (vec K) → (vec K) 
| nat.zero v := vec_zero K
--| 1 v := v
| (nat.succ n) v := (add_vec_vec _) v (nsmul_vec n v)

@[simp]
def gsmul_vec : ℤ → (vec K) → (vec K) 
| (int.of_nat i) v := nsmul_vec K i v
| (int.neg_succ_of_nat i) v := (-(nsmul_vec K i v))
/-
lemma  t : auto_param (∀ (a : vec K), gsmul_vec K 0 a = 0) (name.mk_string "try_refl_tac" name.anonymous) :=
begin
    simp [auto_param],
    intros,
    ext,
    let h0 : (gsmul_vec K 0 a) = 0 := rfl,
    simp *,
    let h0 : (gsmul_vec K 0 a) = 0 := rfl,
    simp *,
end-/

instance : has_add (vec K) := ⟨add_vec_vec K⟩


instance : add_comm_monoid (vec K) :=
⟨
    add_vec_vec K,
    begin
        intros,
        dsimp [has_add.add, add_vec_vec, mk_vec', distrib.add, ring.add, division_ring.add, field.add],
        cases a,
        cases b,
        cases c,
        simp *,
        cc
    end,
    vec_zero K,
    begin
        intros,

        ext,
        exact zero_add _,
        exact zero_add _,
    end,
    begin
        intros,

        ext,
        exact add_zero _,
        exact add_zero _,

    end,
    nsmul_vec K,
    begin
        simp [auto_param],
        dsimp [0, vec_zero K],
        ext,
        cc,
        dsimp [0, vec_zero K],
        cc,
        

    end,
    begin
        simp [auto_param],
        intros,
        ext,
        simp *,
        cc,
        simp *,
        cc,
    end,
    begin
        intros,
        ext,
        exact add_comm _ _,
        exact add_comm _ _,
    end,
⟩

instance : add_monoid (vec K) := 
⟨
add_vec_vec K,
begin
    intros,
    dsimp [has_add.add, add_vec_vec, mk_vec', distrib.add, ring.add, division_ring.add, field.add],
    cases a,
    cases b,
    cases c,
    simp *,
    cc
end,
vec_zero K,
begin
    intros,

    ext,
    exact zero_add _,
    exact zero_add _,
end,
begin
    intros,

    ext,
    exact add_zero _,
    exact add_zero _,

end,
nsmul_vec K
⟩

instance : sub_neg_monoid (vec K) := {
--..(show add_monoid (vec K), by apply_instance),
neg := (neg_vec K),
..(show add_monoid (vec K), by apply_instance),

}

instance : add_group (vec K) := {
add_left_neg := begin
    intros,
    let h0 : (-a + a).to_prod = (-a).to_prod + a.to_prod := rfl,
    let h1 : (0 : vec K).to_prod.fst = 0 := rfl,
    let h2 : (-a).to_prod = -a.to_prod := begin
        --cases a,
        ext,
        simp *,
        let h3 : a.to_prod.fst = 0 := by exact a.inv,
        let h4 : (-a.to_prod.fst) = 0 := begin
            rw h3,
            exact neg_zero,
        end, 
        rw h4,
        exact (-a).inv,
        cases a,
        simp *,
        dsimp [has_neg.neg, sub_neg_monoid.neg, add_group.neg],
        let h5 : add_comm_group.neg 1 * a__to_prod.snd = -a__to_prod.snd := by exact neg_one_mul _,
        simp [h5],
        trivial
    end,

    ext,
    rw [h0],
    rw h1,
    rw h2,
    simp *,
    rw [h0],
    rw h2,
    simp *,
    let h6 : (0 : vec K).to_prod.snd = 0 := rfl,
    simp *,
end,
..(show sub_neg_monoid (vec K), by apply_instance),
}

instance : add_comm_group (vec K) :={
    add_comm := begin
        intros,
        ext,
        exact add_comm _ _,
        exact add_comm _ _,
    end,
..(show add_group (vec K), by apply_instance)
}

instance : has_scalar K (vec K) := ⟨ smul_vec K ⟩

instance : mul_action K (vec K) := 
⟨
begin
    intros,
    cases b,
    ext,
    exact one_mul _,
    exact one_mul _
end, 
begin
    intros,
    cases b,
    ext,
    exact mul_assoc x y _,
    exact mul_assoc x y _
end,
⟩

lemma left_distrib_K_vecK : ∀ (r : K) (x y : vec K), r • (x + y) = r • x + r • y := begin
intros,
        ext,
        exact left_distrib _ _ _,
        exact left_distrib _ _ _
end

instance : distrib_mul_action K (vec K) := 
⟨
    begin
        exact left_distrib_K_vecK K,
        /-intros,
        ext,
        exact left_distrib _ _ _,
        exact left_distrib _ _ _
-/
    end, 
    begin
    intros, ext, exact mul_zero _, exact mul_zero _
    end
⟩

lemma right_distrib_K_vecK : ∀ (r s : K) (x : vec K), (r + s) • x = r • x + s • x := begin
  intros,
  ext,
  exact right_distrib _ _ _,
  exact right_distrib _ _ _


end

instance : module K (vec K) := ⟨
begin
    exact right_distrib_K_vecK K
end,
begin
    intros,
    ext,
    exact zero_mul _, exact zero_mul _
end
⟩


lemma pt_sub_add_cancel : ∀ (p1 p2 : pt K), p1 -ᵥ p2 +ᵥ p2 = p1 := 
begin
intros,
    ext,
    --exact sub_add_cancel _ _ _,

    cases p1,
    cases p2,
    cases p1__to_prod,
    cases p2__to_prod,
    dsimp [has_vadd.vadd, aff_vec_group_action, add_vec_pt, mk_pt'],
    dsimp [has_vsub.vsub, aff_pt_group_sub, sub_pt_pt, mk_vec'],
    dsimp [has_add.add, add_vec_vec, mk_vec', distrib.add, ring.add, has_sub.sub, sub_neg_monoid.sub, add_group.sub, add_comm_group.sub, ring.sub, division_ring.sub, division_ring.add],
    simp * at p2_inv,
    simp * at p1_inv,
    have h1 : p2__to_prod_fst = 1 := by exact p2_inv,
    have h2 : p1__to_prod_fst = 1 := by exact p1_inv,
    simp *,
    have h3 : field.sub (1:K) 1 = 0 := sub_self _,
    simp *,
    exact add_zero _,
    

    cases p1,
    cases p2,
    cases p1__to_prod,
    cases p2__to_prod,
    dsimp [has_vadd.vadd, aff_vec_group_action, add_vec_pt, mk_pt'],
    dsimp [has_vsub.vsub, aff_pt_group_sub, sub_pt_pt, mk_vec'],
    dsimp [has_add.add, add_vec_vec, mk_vec', distrib.add, ring.add, has_sub.sub, sub_neg_monoid.sub, add_group.sub, add_comm_group.sub, ring.sub, division_ring.sub, division_ring.add],
    
    have h4:= sub_add_cancel  p1__to_prod_snd p2__to_prod_snd,
    dsimp [has_add.add, add_zero_class.add, add_vec_vec, mk_vec', add_semigroup.add, add_monoid.add, sub_neg_monoid.add, add_group.add, add_comm_group.add, distrib.add, ring.add, has_sub.sub, sub_neg_monoid.sub, add_group.sub, add_comm_group.sub, ring.sub, division_ring.sub, division_ring.add] at h4,
    have h5 := add_comm_group.add_comm (field.sub p1__to_prod_snd p2__to_prod_snd) p2__to_prod_snd,
    dsimp [has_add.add, add_vec_vec, mk_vec', add_semigroup.add, add_monoid.add, sub_neg_monoid.add, add_group.add, add_comm_group.add, distrib.add, ring.add, has_sub.sub, sub_neg_monoid.sub, add_group.sub, add_comm_group.sub, ring.sub, division_ring.sub, division_ring.add] at h5,

  --  have h6 := add_sub_cancel
    simp [h5] at h4,
    exact h4,
end


lemma zero_vec_vadd'_a1 : ∀ p : pt K, (0 : vec K) +ᵥ p = p := 
begin
    intros,
    ext,--exact zero_add _,
    exact add_zero _,
    exact add_zero _
end

instance : add_action (vec K) (pt K) :=
⟨
begin
    exact zero_vec_vadd'_a1 K
end,
begin
    intros,
    ext,
    cases g₁,
    cases g₂,
    cases p,
    cases g₁__to_prod,
    cases g₂__to_prod,
    cases p__to_prod,
    dsimp [has_vadd.vadd, aff_vec_group_action, add_vec_pt, mk_pt'],
    --simp *,
    dsimp [has_add.add, add_vec_vec, mk_vec', distrib.add, add_zero_class.add, distrib.add, add_monoid.add, ring.add, division_ring.add],
    cc,
    
    cases g₁,
    cases g₂,
    cases p,
    cases g₁__to_prod,
    cases g₂__to_prod,
    cases p__to_prod,
    dsimp [has_vadd.vadd, aff_vec_group_action, add_vec_pt, mk_pt'],
    --simp *,
    dsimp [has_add.add, add_vec_vec, mk_vec', distrib.add, add_zero_class.add, distrib.add, add_monoid.add, ring.add, division_ring.add],
    cc,
    --repeat not working?

end
⟩

instance : nonempty (pt K) := ⟨mk_pt K 1⟩
/-
@[protect_proj] class add_action (G : Type*) (P : Type*) [add_monoid G] extends has_vadd G P :=
(zero_vadd : ∀ p : P, (0 : G) +ᵥ p = p)
(add_vadd : ∀ (g₁ g₂ : G) (p : P), (g₁ + g₂) +ᵥ p = g₁ +ᵥ (g₂ +ᵥ p))
-/

instance vecK_ptK_affine_space : affine_space (vec K) (pt K) := ⟨
    pt_sub_add_cancel K,
    begin
        intros,
        ext,


        cases g,
        cases p,
        cases g__to_prod,
        cases p__to_prod,
        dsimp [has_vadd.vadd, aff_vec_group_action, add_vec_pt, mk_pt'],
        dsimp [has_vsub.vsub, aff_pt_group_sub, sub_pt_pt, mk_vec'],
        dsimp [has_add.add, add_vec_vec, mk_vec', distrib.add, ring.add, has_sub.sub, sub_neg_monoid.sub, add_group.sub, add_comm_group.sub, ring.sub, division_ring.sub, division_ring.add],
        simp * at g_inv,
        simp * at p_inv,
        have h1 : g__to_prod_fst = 0 := by exact g_inv,
        have h2 : p__to_prod_fst = 1 := by exact p_inv,
        simp *,
        have h3 : field.add (1:K) 0 = 1 := add_zero _,
        simp *,
        exact sub_self _,

        cases g,
        cases p,
        cases g__to_prod,
        cases p__to_prod,
        dsimp [has_vadd.vadd, aff_vec_group_action, add_vec_pt, mk_pt'],
        dsimp [has_vsub.vsub, aff_pt_group_sub, sub_pt_pt, mk_vec'],
        dsimp [has_add.add, add_vec_vec, mk_vec', distrib.add, ring.add, has_sub.sub, sub_neg_monoid.sub, add_group.sub, add_comm_group.sub, ring.sub, division_ring.sub, division_ring.add],
        
        have h4:= add_sub_cancel  g__to_prod_snd p__to_prod_snd,
        dsimp [has_add.add, add_vec_vec, mk_vec', add_semigroup.add, add_monoid.add, sub_neg_monoid.add, add_group.add, add_comm_group.add, distrib.add, ring.add, has_sub.sub, sub_neg_monoid.sub, add_group.sub, add_comm_group.sub, ring.sub, division_ring.sub, division_ring.add] at h4,

        cc
    end,
⟩

variables (n : ℕ )
#check  ⨁(i : fin (n)), (λi, vec K) i


#check (pt K) ≃ᵃ[K] (pt K) --works!