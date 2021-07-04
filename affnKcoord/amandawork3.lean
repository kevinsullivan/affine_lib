import data.real.basic
import .affnK
import tactic.linarith
/-
Amanda:

Go to line 730ish and find the proof I just copied and pasted in. It is an example basis proof. 
Dig into the details and you'll be able to adapt this, or at least some of it.
-/
import linear_algebra.basis
-- Testing vec_n_basis

/-
protected noncomputable def span : basis ι R (span R (range v)) :=
basis.mk (linear_independent_span hli) $
begin
  rw eq_top_iff,
  intros x _,
  have h₁ : subtype.val '' set.range (λ i, subtype.mk (v i) _) = range v,
  { rw ← set.range_comp },
  have h₂ : map (submodule.subtype _) (span R (set.range (λ i, subtype.mk (v i) _)))
    = span R (range v),
  { rw [← span_image, submodule.subtype_eq_val, h₁] },
  have h₃ : (x : M) ∈ map (submodule.subtype _) (span R (set.range (λ i, subtype.mk (v i) _))),
  { rw h₂, apply subtype.mem x },
  rcases mem_map.1 h₃ with ⟨y, hy₁, hy₂⟩,
  have h_x_eq_y : x = y,
  { rw [subtype.ext_iff, ← hy₂], simp },
  rwa h_x_eq_y
end
-/

open submodule


def vec_1_basis := 
let v := (λ a : fin 1, (λ b : fin 1, vec.mk (1 : ℚ)))  in
  vec_n_basis.mk v
begin
  ext,
  split,
  {
    intro h,
    dsimp only [has_bot.bot, has_zero.zero, add_zero_class.zero, add_monoid.zero, add_comm_monoid.zero],
    suffices h' : x = {support := ∅, to_fun := λ (_x : fin 1), semiring.zero, mem_support_to_fun := _},
    exact h',
    dsimp only [linear_map.ker, submodule.comap, set.preimage] at h,
    have h₀ : ⇑(finsupp.total (fin 1) (vec_n ℚ 1) ℚ (λ (a b : fin 1), {coord := 1})) x ∈ ↑⊥ := by exact h,
    dsimp only [has_bot.bot, has_zero.zero, add_zero_class.zero, add_monoid.zero, add_comm_monoid.zero] at h₀,
    dsimp only [vec_zero] at h₀,
    have h₁ : ⇑(finsupp.total (fin 1) (vec_n ℚ 1) ℚ (λ (a b : fin 1), {coord := 1})) x = λ (_x : fin 1), mk_vec ℚ 0 := by exact h₀,
    dsimp only [finsupp.total, finsupp.lsum, coe_fn, has_coe_to_fun.coe] at h₁,
    dsimp [finsupp.sum] at h₁,
    simp only [linear_map.id_coe, id.def] at h₁,
    sorry,
  },
  {
    intro h,
    dsimp only [has_bot.bot, has_zero.zero, add_zero_class.zero, add_monoid.zero, add_comm_monoid.zero] at h,
    have h₀ : x = {support := ∅, to_fun := λ (_x : fin 1), semiring.zero, mem_support_to_fun := _} := by exact h,
    dsimp only [linear_map.ker, submodule.comap, set.preimage],
    suffices h' : ⇑(finsupp.total (fin 1) (vec_n ℚ 1) ℚ (λ (a b : fin 1), {coord := 1})) x ∈ ↑⊥,
    exact h',
    dsimp only [has_bot.bot, has_zero.zero, add_zero_class.zero, add_monoid.zero, add_comm_monoid.zero],
    dsimp only [vec_zero],
    suffices h' : ⇑(finsupp.total (fin 1) (vec_n ℚ 1) ℚ (λ (a b : fin 1), {coord := 1})) x = λ (_x : fin 1), mk_vec ℚ 0,
    exact h',
    dsimp only [finsupp.total, finsupp.lsum, coe_fn, has_coe_to_fun.coe],
    rw h₀,
    dsimp [finsupp.sum],
    refl,
  }
end begin
  dsimp only [submodule.span, Inf],
  dsimp only [has_top.top, set.univ],
  dsimp only [coe_sort, has_coe_to_sort.coe, coe, lift_t, has_lift_t.lift, coe_t, has_coe_t.coe, set_like.coe],
  dsimp only [set.range, set.Inter],
  simp only [nonempty_of_inhabited, set.mem_set_of_eq, exists_const],
  ext,
  split,
  {
    intro,
    exact true.intro,
  },
  {
    intro,
    dsimp only [infi, Inf, complete_semilattice_Inf.Inf, complete_lattice.Inf, set.range],
    simp *,
    dsimp [set_of],
    intros f g,
    simp [has_subset.subset, set.subset] at g,
    let h3 := (x ⟨0, by linarith⟩),
    destruct h3,
    intros,
    let one_ : vec_n ℚ 1 := (λ i, {coord := 1}),

    let h4 : one_ ∈ f := by apply @g one_ rfl,
    let onex := coord•one_,
    let onexmem : onex ∈ f := 
      by exact @submodule.smul_mem ℚ (vec_n ℚ 1) _ _ _ f one_ coord h4,
    haveI := onex,
    let h6 : coord • (λ (i : fin 1), {coord := 1} : vec_n ℚ 1) = onex := rfl,
    let onexeq : (∀ (i : fin 1), x i = onex i) := begin
        intros,
        cases i,
        cases i_val,
        { rw ←h6,
          let h7 : (coord • (λ (i : fin 1), {coord := 1}) : vec_n ℚ 1) ⟨0, i_property⟩
            = (coord • {coord := 1}) := begin
              refl
            end,
          simp [h7],
          dsimp [has_scalar.smul],
          simp *,
          let h16 : x 0 = h3 := by refl,
          rw h16,
          exact a,
         },
        {
          cases i_val,
          let h10 : (1 )= (1) := rfl,
          let h11 := lt_irrefl 1,
          contradiction,

          let h12 : 1 < i_val.succ.succ := by exact nat.one_lt_succ_succ i_val,
          let h13 : 1 < 1 := by exact lt_trans h12 i_property,
          let h14 : ¬1<1 := by exact lt_irrefl _,
          contradiction,
        },
    end,
    let h20 : x = onex := by exact funext onexeq,
    rw h20,
    exact onexmem,

  },
end

variables (sm : submodule ℚ (vec_n ℚ 1)) (v : (vec_n ℚ 1))

let h15 := funext one

#check funext
#check (1:ℚ) • v

#check nat.add_succ_lt_add
#check nat.succ_succ_ne_one

#check lt_tra

#check nat.succ_succ

#check lt_add_one

#check nat.succ

#check nat.lt_add_of_zero_lt_left

#check @submodule.smul_mem

#check smul_add

#check finset

#check v ∈ sm

#check (↑sm:set (vec_n ℚ 1)) v

def dajks : fin 2 → ℕ 
| ⟨0, _⟩ := 1
| ⟨1, _⟩ := 2
| ⟨n, _⟩ := 0

#check nat_ceil_lt_add_one
#check nat_mul_inj

#check lt_irrefl

#check lt_add_one
#check submodule

#check module

#check {[1]} ⊆  {[1], [2]}

#check ⦃a : vec_n ℚ 1⦄
  
#check eq_bot_iff

#check eq

#check set.set_of_mem_eq


def n := 1
def K := ℚ


def myfinset : finset ℕ := finset.range 4
@[reducible]
abbreviation pt_nf := ∀i ∈{i|i∈myfinset}, pt ℚ
@[reducible]
abbreviation vec_nf := fin (n) → vec ℚ

#check set.range



#eval 0 ∈ myfinset
#eval myfinset



def mk_pt_nf (vals : vector ℚ n) : pt_nf := 
  λj : _, λmf:_, begin

  end

def mk_vec_nf (vals : vector ℚ n) : vec_nf ℚ n := 
  λi, mk_vec ℚ (vals.nth i)

def pt_nf.coords
 (ptn : pt_nf ) : fin n → ℚ :=
  λi : fin n, (ptn i).coord

def vec_nf.coords (vecn : vec_nf ) : fin n → K :=
  λi, (vecn i).coord


structure vec_nf_basis :=
  (basis_vecs:fin n → vec_nf )
  (basis_independent : linear_independent ℚ basis_vecs)
  (basis_spans : submodule.span ℚ (set.range basis_vecs) = ⊤)

instance : has_lift_t (vec_nf_basis K n) (fin n → vec_n K n) := ⟨λvb, vb.basis_vecs⟩

open_locale affine
--done
instance : add_comm_group (vec_nf) := by apply_instance
instance : affine_space (vec_nf) (pt_nf) := by apply_instance

