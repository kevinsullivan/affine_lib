import .affine
import .list_stuff
import .add_group_action
universes u v w
variables (X : Type u) (K : Type v) (V : Type w) (n : ℕ) (id : ℕ) (k : K)
[inhabited K] [field K] [add_comm_group V] [vector_space K V] [affine_space X K V]
open list
/-- type class for affine vectors. This models n-1 dimensional K-coordinate space. -/
structure aff_vec :=
(l : list K)
(len_fixed : l.length = n + 1)
(fst_zero : head l = 0)
/-- type class for affine points for coordinate spaces. -/
structure aff_pt :=
(l : list K)
(len_fixed : l.length = n + 1)
(fst_one : head l = 1)
variables (x y : aff_vec K n) (a b : aff_pt K n)
-- lemmas so that the following operations are well-defined
/-- the length of the sum of two length n+1 vectors is n+1 -/
lemma list_sum_fixed : length (x.1 + y.1) = n + 1 := 
    by simp only [sum_test K x.1 y.1, length_sum x.1 y.1, x.2, y.2, min_self]
lemma aff_not_nil : x.1 ≠ [] := 
begin
intro h,
have f : 0 ≠ n + 1 := ne.symm (nat.succ_ne_zero n),
have len_x_nil : length x.1 = length nil := by rw h,
have len_fixed : length nil = n + 1 := eq.trans (eq.symm len_x_nil) x.2,
have bad : 0 = n + 1 := eq.trans (eq.symm len_nil) len_fixed,
contradiction,
end
lemma aff_cons : ∃ x_hd : K, ∃ x_tl : list K, x.1 = x_hd :: x_tl :=
begin
cases x,
cases x_l,
{
    have f : 0 ≠ n + 1 := ne.symm (nat.succ_ne_zero n),
    have bad := eq.trans (eq.symm len_nil) x_len_fixed,
    contradiction
},
{
    apply exists.intro x_l_hd,
    apply exists.intro x_l_tl,
    exact rfl
}
end
/-- head is compatible with addition -/
lemma head_sum : head x.1 + head y.1 = head (x.1 + y.1) := 
begin
cases x,
cases y,
cases x_l,
    have f : 0 ≠ n + 1 := ne.symm (nat.succ_ne_zero n),
    have bad := eq.trans (eq.symm len_nil) x_len_fixed,
    contradiction,
cases y_l,
    have f : 0 ≠ n + 1 := ne.symm (nat.succ_ne_zero n),
    have bad := eq.trans (eq.symm len_nil) y_len_fixed,
    contradiction,
have head_xh : head (x_l_hd :: x_l_tl) = x_l_hd := rfl,
have head_yh : head (y_l_hd :: y_l_tl) = y_l_hd := rfl,
rw head_xh at x_fst_zero,
rw head_yh at y_fst_zero,
simp [x_fst_zero, y_fst_zero, sum_test, add_cons_cons 0 0 x_l_tl y_l_tl],
end
/-- the head of the sum of two vectors is 0 -/
lemma sum_fst_fixed : head (x.1 + y.1) = 0 :=
    by simp only [eq.symm (head_sum K n x y), x.3, y.3]; exact add_zero 0
/-- the length of the zero vector is n+1 -/
lemma len_zero : length (field_zero K n) = n + 1 :=
begin
induction n with n',
refl,
{
have h₃ : nat.succ (n' + 1) = nat.succ n' + 1 := rfl,
have h₄ : length (field_zero K (nat.succ n')) = nat.succ (n' + 1) :=
    by {rw eq.symm n_ih, refl},
rw eq.symm h₃,
exact h₄,
}
end
/-- the head of the zero vector is zero -/
lemma head_zero : head (field_zero K n) = 0 := by {cases n, refl, refl}
lemma vec_len_neg : length (neg K x.1) = n + 1 := by {simp only [len_neg], exact x.2}
lemma head_neg_0 : head (neg K x.1) = 0 :=
begin
cases x,
cases x_l,
contradiction,
rw neg_cons K x_l_hd x_l_tl,
have head_xh : head (x_l_hd :: x_l_tl) = x_l_hd := rfl,
have head_0 : head (0 :: neg K x_l_tl) = 0 := rfl,
rw head_xh at x_fst_zero,
simp only [x_fst_zero, neg_zero, head_0],
end
/-! ### abelian group operations -/
def vec_add : aff_vec K n → aff_vec K n → aff_vec K n :=
    λ x y, ⟨x.1 + y.1, list_sum_fixed K n x y, sum_fst_fixed K n x y⟩
def vec_zero : aff_vec K n := ⟨field_zero K n, len_zero K n, head_zero K n⟩
def vec_neg : aff_vec K n → aff_vec K n
| ⟨l, len, fst⟩ := ⟨list.neg K l, vec_len_neg K n ⟨l, len, fst⟩, head_neg_0 K n ⟨l, len, fst⟩⟩
/-! ### type class instances for the abelian group operations -/
instance : has_add (aff_vec K n) := ⟨vec_add K n⟩
instance : has_zero (aff_vec K n) := ⟨vec_zero K n⟩
instance : has_neg (aff_vec K n) := ⟨vec_neg K n⟩
-- misc
def pt_zero_f : ℕ → list K 
| 0 := [1]
| (nat.succ n) := [1] ++ list.field_zero K n
lemma pt_zero_len : length (pt_zero_f K n) = n + 1 := sorry
lemma pt_zero_hd : head (pt_zero_f K n) = 1 := by {cases n, refl, refl} 
def pt_zero : aff_pt K n := ⟨pt_zero_f K n, pt_zero_len K n, pt_zero_hd K n⟩
lemma vec_zero_is : (0 : aff_vec K n) = vec_zero K n := rfl
lemma vec_zero_list' : (0 : aff_vec K n).1 = field_zero K n := rfl
-- properties necessary to show aff_vec K n is an instance of add_comm_group
#print add_comm_group
lemma vec_add_assoc : ∀ x y z : aff_vec K n,  x + y + z = x + (y + z) :=
begin
intros,
cases x,
cases y,
cases z,
induction x_l, contradiction,
induction y_l, contradiction,
induction z_l, contradiction,
sorry, -- issue with these lemmata is the obtuse tactic state. Needs fixing. 
end
lemma vec_zero_add : ∀ x : aff_vec K n, 0 + x = x :=
begin
intro x,
rw vec_zero_is,
-- have sum_len_fixed : length ((vec_zero K n).1 + x.1) = n + 1 := sorry,
-- have sum_fst_zero : head ((vec_zero K n).1 + x.1) = 0 := sorry,
-- have sum_is : vec_zero K n + x = ⟨(vec_zero K n).1 + x.1, sum_len_fixed, sum_fst_zero⟩ := rfl,
have sum_is : vec_zero K n + x = ⟨(vec_zero K n).l + x.1, list_sum_fixed K n (vec_zero K n) x, sum_fst_fixed K n (vec_zero K n) x⟩ := rfl,
have zero_l_is : (vec_zero K n).l = field_zero K n := rfl,
rw sum_is,
-- rw zero_l_is,
sorry
end
lemma vec_zero_add' : ∀ x : aff_vec K n, 0 + x = x :=
begin
intro x,
rw vec_zero_is,
cases x,
cases vec_zero K n with zero_l zero_len_fixed zero_fst_zero,
have sum_len_fixed : length (zero_l + x_l) = n + 1 := sorry,
have sum_fst_zero : head (zero_l + x_l) = 0 := sorry,
-- have sum_is : ⟨zero_l, zero_len_fixed, zero_fst_zero⟩ + ⟨x_l, x_len_fixed, x_fst_zero⟩ = ⟨zero_l + x_l, sum_len_fixed, sum_fst_zero⟩ := rfl,
have zero_l_is : (vec_zero K n).l = field_zero K n := rfl,
-- rw sum_is,
-- rw zero_l_is,
sorry
end
lemma vec_add_zero : ∀ x : aff_vec K n, x + 0 = x :=
begin
intro x,
cases x,
rw vec_zero_is,
cases vec_zero K n with zero_l zero_len_fixed zero_fst_zero,
induction zero_l,
contradiction,
induction x_l,
contradiction,
sorry,
/-
{
    have list_eq : x_l + (zero_l_hd :: zero_l_tl) = x_l :=
        begin
        have zero_list_is : (0 : aff_vec K n).1 = (zero_l_hd :: zero_l_tl) := sorry,
        have zero_vec_zero : (list.cons zero_l_hd zero_l_tl) = field_zero K n :=
            begin
            rw (eq.symm zero_list_is),
            rw vec_zero_list',
            end,
        have vec_field_zero : n = length x_l - 1 := sorry,
        have zero_field_zero : (list.cons zero_l_hd zero_l_tl) = field_zero K (length x_l - 1) :=
            begin
            rw (eq.symm vec_field_zero),
            exact zero_vec_zero
            end,
        rw zero_field_zero,
        apply list.add_zero,
        end,
    {sorry}
}
-/
end
lemma vec_add_left_neg : ∀ x : aff_vec K n, -x + x = 0 :=
begin
intro x,
cases x,
rw vec_zero_is,
cases vec_zero K n with zero_l zero_len_fixed zero_fst_zero,
have x_not_nil : x_l ≠ nil :=
    begin
    induction x_l,
    {contradiction},
    {simp}
    end,
have zero_not_nil : zero_l ≠ nil :=
    begin
    induction zero_l,
    {contradiction},
    {simp}
    end,
-- have neg_x_is : - ⟨x_l, x_len_fixed, x_fst_zero⟩ = ⟨- x_l, vec_len_neg K n ⟨x_l, x_len_fixed, x_fst_zero⟩, head_neg_0 K n ⟨x_l, x_len_fixed, x_fst_zero⟩⟩ := rfl,
-- rw neg_x_is,
sorry
end
lemma vec_add_comm : ∀ x y : aff_vec K n, x + y = y + x :=
begin
intros x y,
cases x,
cases y,
induction x_l,
contradiction,
induction y_l,
contradiction,
repeat{sorry},
end
/-! ### Type class instance for abelian group -/
instance : add_comm_group (aff_vec K n) :=
begin
split,
exact vec_add_left_neg K n,
exact vec_add_comm K n,
exact vec_add_assoc K n,
exact vec_zero_add K n,
exact vec_add_zero K n,
end
/-! ### Scalar action -/
#check semimodule
#check distrib_mul_action
lemma scale_head : head (field_scalar K k x.1) = 0 :=
begin
cases x,
cases x_l,
rw scalar_nil,
contradiction,
have hd0 : x_l_hd = 0 := x_fst_zero,
rw [scalar_cons, hd0, mul_zero],
refl,
end
def vec_scalar : K → aff_vec K n → aff_vec K n :=
    λ a x, ⟨field_scalar K a x.1, trans (scale_len K a x.1) x.2, scale_head K n a x⟩
instance : has_scalar K (aff_vec K n) := ⟨vec_scalar K n⟩
lemma vec_one_smul : (1 : K) • x = x := sorry
lemma vec_mul_smul : ∀ g h : K, ∀ x : aff_vec K n, (g * h) • x = g • h • x := sorry
instance : mul_action K (aff_vec K n) := ⟨vec_one_smul K n, vec_mul_smul K n⟩
lemma vec_smul_add : ∀ g : K, ∀ x y : aff_vec K n, g • (x + y) = g•x + g•y := sorry
lemma vec_smul_zero : ∀ g : K, g • (0 : aff_vec K n) = 0 := sorry
instance : distrib_mul_action K (aff_vec K n) := ⟨vec_smul_add K n, vec_smul_zero K n⟩
lemma vec_add_smul : ∀ g h : K, ∀ x : aff_vec K n, (g + h) • x = g•x + h•x := sorry
lemma vec_zero_smul : ∀ x : aff_vec K n, (0 : K) • x = 0 := sorry
instance : semimodule K (aff_vec K n) := ⟨vec_add_smul K n, vec_zero_smul K n⟩
instance aff_module : module K (aff_vec K n) := module.mk
-- need to define scalar multiplication to show it's a module
instance : vector_space K (aff_vec K n) := aff_module K n
/-! ### group action of aff_vec on aff_pt -/
-- need to actually write out the function
def aff_group_action : aff_vec K n → aff_pt K n → aff_pt K n :=
    λ x y, sorry
instance : has_trans (aff_vec K n) (aff_pt K n) := ⟨aff_group_action K n⟩
lemma aff_zero_sadd : ∀ x : aff_pt K n, (0 : aff_vec K n) ⊹ x = x := sorry
lemma aff_add_sadd : ∀ x y : aff_vec K n, ∀ a : aff_pt K n, (x + y) ⊹ a = x ⊹ y ⊹ a := sorry
instance : add_action (aff_vec K n) (aff_pt K n) := ⟨aff_zero_sadd K n, aff_add_sadd K n⟩
instance : add_space (aff_vec K n) (aff_pt K n) := add_space.mk
lemma aff_add_trans : ∀ a b : aff_pt K n, ∃ x : aff_vec K n, x ⊹ a = b := sorry
instance : add_homogeneous_space (aff_vec K n) (aff_pt K n) := ⟨aff_add_trans K n⟩
lemma aff_add_free : ∀ a : aff_pt K n, ∀ g h : aff_vec K n, g ⊹ a = h ⊹ a → g = h := sorry
instance aff_torsor : add_torsor (aff_vec K n) (aff_pt K n) := ⟨aff_add_free K n⟩
-- WTS the pair aff_vec and aff_pt form an affine space
instance : affine_space (aff_pt K n) K (aff_vec K n) := aff_torsor K n
-- Different file, physical quantities
/-
def time' := space.mk 1
def geom3 := space.mk 2
def duration := aff_vec ℝ 1 time'
def time     := aff_pt  ℝ 1 time'
noncomputable def std_origin : time := ⟨[1, 0], rfl, rfl⟩
def length   := aff_vec ℝ 3 geom3
def phys_pt  := aff_pt  ℝ 3 geom3
-/
-- WTS the pair aff_vec and aff_pt form an affine space
instance aff_coord_inst : affine_space (aff_pt K n) K (aff_vec K n) := aff_torsor K n

