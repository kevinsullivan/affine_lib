import data.real.basic
import .affnK
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
    simp only [forall_apply_eq_imp_iff', and_imp, set_like.mem_coe, submodule.mem_carrier, set.mem_set_of_eq, exists_imp_distrib, exists_const],
    suffices h : ∀ (a_1 : submodule ℚ (vec_n ℚ 1)), set_of (eq (λ (b : fin 1), ({coord := 1} : vec ℚ))) ⊆ a_1.carrier → x ∈ a_1,
    exact h,
    intros a_1 h,
    dsimp only [set_of] at h,
    dsimp only [has_subset.subset, set.subset] at h,
    
  },
end
  