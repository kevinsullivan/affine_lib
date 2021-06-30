import data.real.basic
import .affnK

-- Testing vec_n_basis

def vec_1_basis := vec_n_basis.mk (λ a : fin 1, (λ b : fin 1, vec.mk (1 : ℚ))) begin
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
  dsimp only [coe_sort, has_coe_to_sort.coe, coe, lift_t, has_lift_t.lift, coe_t, has_coe_t.coe, set_like.coe],
  sorry,
end