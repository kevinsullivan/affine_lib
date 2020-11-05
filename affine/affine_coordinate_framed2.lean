import .list_as_k_tuple linear_algebra.affine_space.basic
import linear_algebra.basis
import .affine_coordinate_space
import data.real.basic



open list
open vecl

namespace aff_fr

universes u v w

variables 
    -- (id : ℕ)
    (X : Type u) 
    (K : Type v) 
    (V : Type w) 
    (n : ℕ) 
    (k : K)
    (ι : Type*)
    (s : finset ι) 
    (g : ι → K) 
    (v : ι → V) 
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    [is_basis K v] 
    [affine_space V X]

/-
An affine frame comprises an origin point
and a basis for the vector space.
-/
structure affine_frame :=
(origin : X)
(basis : ι → V)
(proof_is_basis : is_basis K basis)


/-
To do: Look at using inheritance to make everything easier?
-/

/-- type of affine vectors represented by coordinate tuples -/
@[ext]
structure av
    {x : Type u}
    {k : Type v}
    {v : Type w}
    {dim : ℕ}
    {ι : Type*}
    [inhabited k] 
    [field k] 
    [add_comm_group v] 
    [module k v] 
    [vector_space k v] 
    [affine_space v x]
    (frame : affine_frame x k v ι)  :=
(tuple : aff_vec_coord_tuple k dim)

@[ext]
structure ap
    {x : Type u}
    {k : Type v}
    {v : Type w}
    (dim : ℕ)
    {ι : Type*}
    [inhabited k] 
    [field k] 
    [add_comm_group v] 
    [module k v] 
    [vector_space k v] 
    [affine_space v x]
    (frame : affine_frame x k v ι)  :=
(tuple : aff_vec_coord_tuple k dim)


/-- type of affine points represented by coordinate tuples -/

@[ext]
structure aff_coord_pt (frame : affine_frame X K V ι) :=
(tuple : aff_pt_coord_tuple K n)



/-- type of affine points represented by coordinate tuples -/

@[ext]
structure aff_coord_vec (frame : affine_frame X K V ι) :=
(tuple : aff_vec_coord_tuple K n)


variables 
    (fr : affine_frame X K V ι) 
    (cv1 cv2 : aff_coord_vec X K V n ι fr) 
    (cp1 cp2 : aff_coord_pt  X K V n ι fr)

variables
    (a1 : av (fr))

abbreviation vec_type := aff_coord_vec X K V n ι fr
abbreviation pt_type := aff_coord_pt X K V n ι fr

instance ag : add_group (aff_coord_vec X K V n ι fr) := sorry

-- lemmas so that the following operations are well-defined
/-- the length of the sum of two length n+1 vectors is n+1 -/
lemma list_sum_fixed_coord : length (ladd cv1.tuple.1 cv2.tuple.1) = n + 1 := 
    by simp only [length_sum cv1.tuple.1 cv2.tuple.1, cv1.tuple.2, cv2.tuple.2, min_self]

lemma aff_not_nil_coord : cv1.tuple.1 ≠ [] := 
begin
    sorry
end

lemma aff_cons_coord : ∃ x_hd : K, ∃ x_tl : list K, cv1.tuple.1 = x_hd :: x_tl :=
begin
    sorry
end

/-- head is compatible with addition -/
lemma head_sum_coord : head cv1.tuple.1 + head cv2.tuple.1 = head (ladd cv1.tuple.1 cv2.tuple.1) := 
begin
sorry
end
/-- the head of the sum of two vectors is 0 -/
lemma sum_fst_fixed_coord : head (ladd cv1.tuple.1 cv2.tuple.1) = 0 :=
    by simp only [eq.symm (head_sum_coord X K V n ι fr cv1 cv2), cv1.tuple.3, cv2.tuple.3]; exact add_zero 0

/-- the length of the zero vector is n+1 -/
lemma len_zero_coord : length (zero_vector K n) = n + 1 :=
begin
    sorry
end

/-- the head of the zero vector is zero -/
lemma head_zero_coord : head (zero_vector K n) = 0 := by {cases n, refl, refl}

lemma vec_len_neg_coord : length (vecl_neg cv1.tuple.1) = n + 1 := by {simp only [len_neg], exact cv1.tuple.2}

lemma head_neg_0_coord : head (vecl_neg cv1.tuple.1) = 0 :=
begin
    sorry
end

/-! ### abelian group operations -/
def vec_add_coord : aff_coord_vec X K V n ι fr → aff_coord_vec X K V n ι fr → aff_coord_vec X K V n ι fr :=
    λ x y, 
    ⟨⟨ladd x.tuple.1 y.tuple.1, 
        list_sum_fixed_coord X K V n ι fr x y, 
        sum_fst_fixed_coord X K V n ι fr x y⟩⟩
def vec_zero_coord : aff_coord_vec X K V n ι fr := ⟨⟨zero_vector K n, len_zero K n, head_zero K n⟩⟩
def vec_neg_coord : aff_coord_vec X K V n ι fr → aff_coord_vec X K V n ι fr
| ⟨⟨l, len, fst⟩⟩ := ⟨⟨vecl_neg l, vec_len_neg_coord X K V n ι fr ⟨⟨l, len, fst⟩⟩, head_neg_0_coord X K V n ι fr ⟨⟨l, len, fst⟩⟩⟩⟩

/-! ### type class instances for the abelian group operations -/
instance : has_add (aff_coord_vec X K V n ι fr) := ⟨vec_add_coord X K V n ι fr⟩
instance : has_zero (aff_coord_vec X K V n ι fr) := ⟨vec_zero_coord X K V n ι fr⟩
instance : has_neg (aff_coord_vec X K V n ι fr) := ⟨vec_neg_coord X K V n ι fr⟩

-- misc
def pt_zero_f_coord : ℕ → list K
| 0 := [1]
| (nat.succ n) := [1] ++ zero_vector K n

lemma pt_zero_len_coord : length (pt_zero_f K n) = n + 1 := sorry

lemma pt_zero_hd_coord : head (pt_zero_f K n) = 1 := by {cases n, refl, refl} 

def pt_zero_coord : aff_pt_coord_tuple K n := ⟨pt_zero_f K n, pt_zero_len K n, pt_zero_hd K n⟩

lemma vec_zero_is_coord : (0 : aff_coord_vec X K V n ι fr) = vec_zero_coord X K V n ι fr := rfl

lemma vec_zero_list_coord' : (0 : aff_coord_vec X K V n ι fr).tuple.1 = zero_vector K n := sorry

-- properties necessary to show aff_vec_coord_tuple K n is an instance of add_comm_group
#print add_comm_group
lemma vec_add_assoc_coord : ∀ x y z : aff_coord_vec X K V n ι fr,  x + y + z = x + (y + z) :=
begin
intros,
cases x,
cases y,
cases z,
induction x,
induction y,
induction z,
dsimp [has_add.add, vec_add_coord],
ext,
split,
intros,
dsimp [ladd, has_add.add] at a_1,
sorry, sorry,
end

lemma vec_zero_add_coord : ∀ x : aff_coord_vec X K V n ι fr, 0 + x = x :=
begin
intro x,
cases x,
induction x,
rw vec_zero_is_coord,
ext,
split,
intros,
dsimp [has_add.add, vec_add, vec_zero] at a_1,
change a ∈ (ladd (zero_vector K n) x_l).nth n_1 at a_1,
rw zero_ladd' x_l n x_len_fixed at a_1,
exact a_1,

intros,
dsimp [has_add.add, vec_add, vec_zero],
change a ∈ (ladd (zero_vector K n) x_l).nth n_1,
rw zero_ladd' x_l n x_len_fixed,
exact a_1,
end

lemma vec_add_zero_coord : ∀ x : aff_coord_vec X K V n ι fr, x + 0 = x :=
begin
intro x,
cases x,
induction x,
rw vec_zero_is_coord,
ext,
split,
intros,
dsimp [has_add.add, vec_add, vec_zero] at a_1,
change a ∈ (ladd x_l (zero_vector K n)).nth n_1 at a_1,
rw ladd_zero' x_l n x_len_fixed at a_1,
exact a_1,

intros,
dsimp [has_add.add, vec_add, vec_zero],
change a ∈ (ladd x_l (zero_vector K n)).nth n_1,
rw ladd_zero' x_l n x_len_fixed,
exact a_1,
end

lemma vec_add_left_neg_coord : ∀ x : aff_coord_vec X K V n ι fr, -x + x = 0 :=
begin
intro x,
cases x,
induction x,
rw vec_zero_is_coord,
ext,
split,
intros,
dsimp [vec_zero_coord],
dsimp [has_neg.neg, vec_neg, has_add.add, vec_add] at a_1,
cases x_l,
contradiction,
have nz : n + 1 ≠ 0 := nat.succ_ne_zero n,
have hnz : (cons x_l_hd x_l_tl).length ≠ 0 := ne_of_eq_of_ne x_len_fixed nz,
change a ∈ (ladd (vecl_neg (x_l_hd :: x_l_tl)) (x_l_hd :: x_l_tl)).nth n_1 at a_1,
rw ladd_left_neg (cons x_l_hd x_l_tl) at a_1,
dsimp [zero_vector] at a_1,
simp only [nat.add_succ_sub_one, add_zero] at a_1,
sorry,
contradiction,
intros,
sorry,
end

lemma vec_add_comm_coord : ∀ x y : aff_coord_vec X K V n ι fr, x + y = y + x :=
begin
intros x y,
cases x,
cases y,
induction x,
induction y,
ext,
split,
intros,
dsimp [has_add.add, vec_add],
dsimp [has_add.add, vec_add] at a_1,
change a ∈ (ladd y_l x_l).nth n_1,
rw ladd_comm,
exact a_1,

intros,
dsimp [has_add.add, vec_add],
dsimp [has_add.add, vec_add] at a_1,
change a ∈ (ladd x_l y_l).nth n_1,
rw ladd_comm,
exact a_1,
end

/-! ### Type class instance for abelian group -/
instance aff_comm_group_coord : add_comm_group (aff_coord_vec X K V n ι fr) :=
begin
split,
exact vec_add_left_neg_coord X K V n ι fr,
exact vec_add_comm_coord X K V n ι fr,
exact vec_add_assoc_coord X K V n ι fr,
exact vec_zero_add_coord X K V n ι fr,
exact vec_add_zero_coord X K V n ι fr,
end



/-! ### Scalar action -/
#check semimodule
#check distrib_mul_action
lemma scale_head_coord : ∀ a : K, head (scalar_mul a cv1.tuple.1) = 0 :=
begin
intros,
cases cv1,
induction cv1,
cases cv1_l,
rw scalar_nil,
contradiction,
have hd0 : cv1_l_hd = 0 := cv1_fst_zero,
rw [scalar_cons, hd0, mul_zero],
refl,
end

@[ext]
def vec_scalar_coord : K → aff_coord_vec X K V n ι fr → aff_coord_vec X K V n ι fr :=
    λ a x, ⟨⟨scalar_mul a x.tuple.1, trans (scale_len a x.tuple.1) x.tuple.2, scale_head_coord X K V n ι fr x a⟩⟩

--instance : has_scalar K (aff_vec_coord_tuple K n) := ⟨vec_scalar K n⟩
instance : has_scalar K (aff_coord_vec X K V n ι fr) := ⟨vec_scalar_coord X K V n ι fr⟩

lemma vec_one_smul_coord : (1 : K) • cv1 = cv1 := 
begin
/-cases cv1,
ext,
split,
intros,
dsimp only [has_scalar.smul, vec_scalar] at a_1,-/
sorry--rw one_smul_cons at a_1,
--exact a_1,
/-
intros,
dsimp only [has_scalar.smul, vec_scalar],
rw one_smul_cons,
exact a_1,-/
end

lemma vec_mul_smul_coord : ∀ g h : K, ∀ x : aff_coord_vec X K V n ι fr, (g * h) • x = g • h • x := sorry

instance : mul_action K (aff_coord_vec X K V n ι fr) := ⟨vec_one_smul_coord X K V n ι fr, vec_mul_smul_coord X K V n ι fr⟩

lemma vec_smul_add_coord : ∀ r : K, ∀ x y 
    : aff_coord_vec X K V n ι fr, r • (x + y) = r•x + r•y := sorry

lemma vec_smul_zero_coord : ∀ r : K, r • (0 : aff_coord_vec X K V n ι fr) = (0 : aff_coord_vec X K V n ι fr) := sorry

/-
∀ (r : K) (x y : @aff_coord_vec X K V n ι 
_inst_1 _inst_2 _inst_3 _inst_5 _inst_5 _inst_8 _inst_8 fr),
    @eq (@aff_coord_vec X K V n ι 
_inst_1 _inst_2 _inst_3 _inst_5 _inst_5 _inst_8 _inst_8 fr)
-/
/-but is expected to have type
  ∀ (r : K) (x y : @aff_coord_vec X K V n ι 
  _inst_1 _inst_2 _inst_3 _inst_5 _inst_5 _inst_8 _inst_8 fr)
  -/
lemma vec_add_smul_coord : ∀ g h : K, ∀ x : (aff_coord_vec X K V n ι fr), (g + h) • x = g•x + h•x := sorry

lemma vec_zero_smul_coord : ∀ x : (aff_coord_vec X K V n ι fr), (0 : K) • x = 0 := sorry

instance : distrib_mul_action K (aff_coord_vec X K V n ι fr) := 
    sorry
instance aff_semimod_coord : semimodule K (aff_coord_vec X K V n ι fr) := 
    -- extremely odd that this doesnt work....
    ⟨vec_add_smul_coord X K V n ι fr, vec_zero_smul_coord X K V n ι fr⟩
/-
failed to synthesize type class instance for
distrib_mul_action K (aff_coord_vec X K V n ι fr)
-/


/-
@[protect_proj] class semimodule (R : Type u) (M : Type v) [semiring R]
  [add_comm_monoid M] extends distrib_mul_action R M :=
(add_smul : ∀(r s : R) (x : M), (r + s) • x = r • x + s • x)
(zero_smul : ∀x : M, (0 : R) • x = 0)
end prio
-/


instance aff_module_coord : module K (aff_coord_vec X K V n ι fr) := sorry--aff_semimod_coord X K V n ι fr

/-! ### group action of aff_vec_coord_tuple on aff_pt_coord_tuple -/
-- need to actually write out the function
def aff_group_action_coord : aff_coord_vec X K V n ι fr → aff_coord_pt X K V n ι fr → aff_coord_pt X K V n ι fr :=
    λ x y, ⟨⟨ladd x.tuple.1 y.tuple.1, sorry, sorry⟩⟩

def aff_group_sub_coord : aff_coord_pt X K V n ι fr → aff_coord_pt X K V n ι fr → aff_coord_vec X K V n ι fr :=
    λ x y, ⟨⟨ladd x.tuple.1 (vecl_neg y.tuple.1), sorry, sorry⟩⟩

#check add_action

instance : has_vadd (aff_coord_vec X K V n ι fr) (aff_coord_pt X K V n ι fr) := ⟨aff_group_action_coord X K V n ι fr⟩

instance : has_vsub (aff_coord_vec X K V n ι fr) (aff_coord_pt X K V n ι fr) := ⟨aff_group_sub_coord X K V n ι fr⟩

lemma aff_zero_sadd_coord : ∀ x : aff_coord_pt X K V n ι fr, (0 : aff_coord_vec X K V n ι fr) +ᵥ x = x := sorry

lemma aff_add_sadd_coord : ∀ x y : aff_coord_vec X K V n ι fr, ∀ a : aff_coord_pt X K V n ι fr, x +ᵥ (y +ᵥ a) = x + y +ᵥ a := sorry

instance : add_action (aff_coord_vec X K V n ι fr) (aff_coord_pt X K V n ι fr) := sorry--⟨aff_group_action_coord X K V n ι fr, aff_zero_sadd_coord X K V n ι fr, aff_add_sadd_coord X K V n ι fr⟩

lemma aff_add_trans_coord : ∀ a b : aff_coord_pt X K V n ι fr, ∃ x : aff_coord_vec X K V n ι fr, x +ᵥ a = b := sorry

lemma aff_add_free_coord : ∀ a : aff_coord_pt X K V n ι fr, ∀ g h :aff_coord_vec X K V n ι fr, g +ᵥ a = h +ᵥ a → g = h := sorry

lemma aff_vadd_vsub_coord : ∀ a b : aff_coord_pt X K V n ι fr, a -ᵥ b +ᵥ b = a := sorry


/-
We need proof that given a frame f, 
⟨ aff_coord_pt f, aff_coord_vec f⟩ is 
an affine space,
-/

--instance 
--instance att : add_torsor (aff_coord_vec X K V n ι fr) (aff_coord_pt  X K V n ι fr) := 
--    sorry    

def prf : affine_space (aff_coord_vec X K V n ι fr) (aff_coord_pt  X K V n ι fr) := sorry

instance afc : affine_space 
    (aff_coord_vec X K V n ι fr) 
    (aff_coord_pt  X K V n ι fr) := 
    prf X K V n ι fr


/-
KEEP?
-/
def affine_coord_tuple_space_type (K : Type v) (n : ℕ) [field K] [inhabited K] := 
    affine_space_type 
        (aff_pt_coord_tuple K n)
        K
        (aff_vec_coord_tuple K n)

def affine_coord_space_type 
    {X : Type u} {K : Type v} {V : Type w} {n : ℕ} {ι : Type*} {b : ι → V} 
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    [affine_space V X]
    
    (fr : affine_frame X K V ι)  := 
    affine_space_type 
        (aff_coord_pt X K V n ι fr)
        K
        (aff_coord_vec X K V n ι fr)


/-
Code to manufacture a standard basis for a given affine space.
-/
abbreviation zero := zero_vector K n

def list.to_basis_vec : fin n → list K := λ x, (zero K n).update_nth (x.1 + 1) 1

lemma len_basis_vec_fixed (x : fin n) : (list.to_basis_vec K n x).length = n + 1 := sorry

lemma head_basis_vec_fixed (x : fin n) : (list.to_basis_vec K n x).head = 0 := sorry

def std_basis : fin n → aff_vec_coord_tuple K n :=
λ x, ⟨list.to_basis_vec K n x, len_basis_vec_fixed K n x, head_basis_vec_fixed K n x⟩

lemma std_is_basis : is_basis K (std_basis K n) := sorry

def aff_coord_space_std_frame : 
    affine_frame (aff_pt_coord_tuple K n) K (aff_vec_coord_tuple K n) (fin n) := 
        ⟨pt_zero K n, std_basis K n, std_is_basis K n⟩

end aff_fr