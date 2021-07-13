import ..affnKcoord.affnKcoord_transforms
import data.real.basic
import linear_algebra.affine_space.basic
import topology.metric_space.emetric_space
import analysis.normed_space.inner_product
import data.complex.is_R_or_C
import topology.metric_space.pi_Lp
import data.real.nnreal

open_locale big_operators
open_locale nnreal

open ennreal

abbreviation K := ℝ

variables
{dim : nat} {id_vec : fin dim → nat }{f : fm K dim id_vec} (s : spc K f)
{dim2 : nat } {id_vec2 : fin dim → nat} {f2 : fm K dim id_vec} (s2 : spc K f2)


noncomputable def dot_product_coord
  : vectr s → vectr s → ℝ
| v1 v2 := 
    (∑ (i : fin dim), ↑((v1.coords i).coord * (v1.coords i).coord))

    

noncomputable def norm_coord
  : vectr s → ℝ
| v1 := 
    real.sqrt (dot_product_coord _ v1 v1)

noncomputable instance vectr_norm : has_norm (vectr s) := ⟨norm_coord s⟩

noncomputable instance vectr_inner : has_inner ℝ (vectr s) := ⟨dot_product_coord s⟩

notation `⟪`x`, `y`⟫` := has_inner.inner x y

noncomputable
def l2_metric
  : point s → point s → ℝ
| pt1 pt2 := ∥pt1 -ᵥ pt2∥

noncomputable
def l2_extended_metric
  : point s → point s → ennreal
| pt1 pt2 := option.some (⟨∥pt1 -ᵥ pt2∥,begin
  dsimp only [has_norm.norm, norm_coord],
  apply real.sqrt_nonneg,
end⟩:(ℝ≥0))

noncomputable
instance euclidean_distance_coord : has_dist (point s) := ⟨l2_metric s⟩ 

noncomputable
instance euclidean_extended_distance_coord : has_edist (point s) := ⟨l2_extended_metric s⟩

/-
structure emetric_space (α : Type u) :
Type u
to_has_edist : has_edist α
edist_self : ∀ (x : α), edist x x = 0
eq_of_edist_eq_zero : ∀ {x y : α}, edist x y = 0 → x = y
edist_comm : ∀ (x y : α), edist x y = edist y x
edist_triangle : ∀ (x y z : α), edist x z ≤ edist x y + edist y z
to_uniform_space : uniform_space α
uniformity_edist : (𝓤 α = ⨅ (ε : ennreal) (H : ε > 0), 𝓟 {p : α × α | edist p.fst p.snd < ε}) . "control_laws_tac"
-/
/-
class metric_space (α : Type u) extends has_dist α : Type u :=
(dist_self : ∀ x : α, dist x x = 0)
(eq_of_dist_eq_zero : ∀ {x y : α}, dist x y = 0 → x = y)
(dist_comm : ∀ x y : α, dist x y = dist y x)
(dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z)
(edist : α → α → ennreal := λx y, ennreal.of_real (dist x y))
(edist_dist : ∀ x y : α, edist x y = ennreal.of_real (dist x y) . control_laws_tac)
(to_uniform_space : uniform_space α := uniform_space_of_dist dist dist_self dist_comm dist_triangle)
(uniformity_dist : 𝓤 α = ⨅ ε>0, 𝓟 {p:α×α | dist p.1 p.2 < ε} . control_laws_tac)


-/
/-


-/
--#eval noncomputable_value -- doesn't work


noncomputable instance euclidean_pseudo_metric_space_pt : pseudo_metric_space (point s)
  := ⟨begin
    intros,
    dsimp only [dist, l2_metric, norm, norm_coord, 
      has_vsub.vsub, aff_point_group_sub, sub_point_point, 
      mk_vectr', aff_pt_group_sub, sub_pt_pt],
    simp,
    simp only [real.sqrt_mul, real.sqrt_eq_zero, nat.cast_eq_zero, nat.cast_nonneg, mul_eq_zero],
    --apply or.inr,
   -- have h₁ : ↑0 = 0 := by simp only [nat.cast_id],
   -- have h₂ : real.sqrt ↑0 = real.sqrt 0 := by simp only [nat.cast_zero],
    --sorry,
  end, begin
    intros,
    dsimp only [dist, l2_metric, norm, norm_coord, 
      has_vsub.vsub, aff_point_group_sub, sub_point_point, 
      mk_vectr', aff_pt_group_sub, sub_pt_pt],
    have h₀ : ∀ i : fin dim, (x.coords i).coord - (y.coords i).coord = -1 * ((y.coords i).coord - (x.coords i).coord) := sorry,
    suffices h : ∀ i : fin dim, ((x.coords i).coord - (y.coords i).coord) * ((x.coords i).coord - (y.coords i).coord) = ((y.coords i).coord - (x.coords i).coord) * ((y.coords i).coord - (x.coords i).coord),
    sorry,
    {
      intros,
      rw h₀,
      have h₁ : (-1) * ((y.coords i).coord - (x.coords i).coord) * ((-1) * ((y.coords i).coord - (x.coords i).coord)) = (-1) * ((y.coords i).coord - (x.coords i).coord) * (-1) * ((y.coords i).coord - (x.coords i).coord) := by simp only [mul_assoc],
      rw h₁,
      simp only [mul_comm],
      have h₂ : ((y.coords i).coord - (x.coords i).coord) * ((-1) * ((-1) * ((y.coords i).coord - (x.coords i).coord))) = ((y.coords i).coord - (x.coords i).coord) * ((-1) * (-1) * ((y.coords i).coord - (x.coords i).coord)) := by simp only [neg_mul_eq_neg_mul_symm, one_mul],
      rw h₂,
      simp only [mul_one, one_mul, mul_neg_eq_neg_mul_symm, neg_neg],
    }
  end, begin
    intros,
    dsimp only [dist, l2_metric, norm, norm_coord, 
      has_vsub.vsub, aff_point_group_sub, sub_point_point, 
      mk_vectr', aff_pt_group_sub, sub_pt_pt],
    sorry,
  end, sorry, sorry, sorry, sorry⟩

instance euclidean_dist_vec : has_dist (vectr s)
  := ⟨sorry⟩

instance euclidean_pseudo_metric_space_vec : pseudo_metric_space (vectr s)
  := ⟨sorry, sorry, sorry, sorry, sorry, sorry, sorry⟩

instance euclidean_metric_space_pt : metric_space (point s)
  := ⟨begin
    intros x y h,
    dsimp only [dist, l2_metric, norm, norm_coord, 
      has_vsub.vsub, aff_point_group_sub, sub_point_point, 
      mk_vectr', aff_pt_group_sub, sub_pt_pt] at h,
    have h₀ : ∀ r : ℝ, r ^ (1/2) = real.sqrt r := sorry,
    rw h₀ at h,
    have h₁ := real.sqrt_eq_zero'.1 h,
    have h₂ : ∀ r : ℝ, r ≥ 0 → ∑ (i : fin dim), r ≥ 0 := sorry,
    have h₃ : ∀ r : ℝ, r * r ≥ 0 := sorry,
    -- have h₄ : ∀ (i : fin dim), ((x.coords i).coord - (y.coords i).coord) * ((x.coords i).coord - (y.coords i).coord) ≥ 0 := sorry,
    sorry,
  end⟩

instance euclidean_metric_space_vec : metric_space (vectr s)
  := ⟨begin
    intros x y h,
    sorry,
  end⟩

instance euclidean_pseudo_extended_metric_space_pt : pseudo_emetric_space (point s) 
  := ⟨begin
    intros,
    dsimp only [edist, l2_extended_metric],
    simp only [some_eq_coe, coe_eq_zero],
    dsimp only [has_zero.zero],
    simp only [subtype.mk_eq_mk],
    dsimp only [has_norm.norm, norm_coord],
    have h₀ : ∀ r : ℝ, r ^ (1/2) = real.sqrt r := sorry,
    rw h₀,
    --simp only [real.sqrt_eq_zero'],
    dsimp only [has_vsub.vsub, aff_point_group_sub, sub_point_point, aff_pt_group_sub, sub_pt_pt, mk_vectr'],
    simp,
    /- have h₁ : ↑dim * ↑0 = 0 := by simp,
    dsimp only [has_le.le],-/
    /-have h₁ : real.sqrt ↑dim * real.sqrt ↑0 = 0 := by simp only [real.sqrt_zero, nat.cast_zero, mul_zero],
    rw h₁,-/
    sorry,
  end, begin
    intros,
    dsimp only [edist, l2_extended_metric],
    simp only [coe_eq_coe, subtype.mk_eq_mk, some_eq_coe],
    dsimp only [norm, norm_coord],
    have h₀ : ∀ r : ℝ, r ^ (1/2) = real.sqrt r := sorry,
    repeat {rw h₀},
    sorry,
  end, begin
    intros,
    dsimp only [edist, l2_extended_metric],
    simp only [some_eq_coe],
    sorry,
  end, sorry, sorry⟩

instance euclidean_pseudo_extended_metric_space_vec : pseudo_emetric_space (vectr s)
  := ⟨sorry, sorry, sorry, sorry, sorry⟩

noncomputable
instance euclidean_extended_metric_space_pt : emetric_space (point s) 
  := ⟨begin
    intros x y h,
    dsimp only [edist, l2_extended_metric] at h,
    simp only [some_eq_coe, coe_eq_zero] at h,
    dsimp only [has_zero.zero] at h,
    simp only [subtype.mk_eq_mk] at h,
    dsimp only [has_norm.norm, norm_coord] at h,
    have h₀ : ∀ r : ℝ, r ^ (1/2) = real.sqrt r := sorry,
    rw h₀ at h,
    sorry
  end⟩

noncomputable
instance euclidean_extended_metric_space_vec : emetric_space (vectr s) 
  := ⟨sorry⟩


noncomputable
instance euclidean_extended_metric_space : emetric_space (point s) 
  := ⟨begin
    intros x y h,
    dsimp only [edist, l2_extended_metric] at h,
    simp only [some_eq_coe, coe_eq_zero] at h,
    dsimp only [has_zero.zero] at h,
    simp only [subtype.mk_eq_mk] at h,
    dsimp only [has_norm.norm, norm_coord] at h,
    have h₀ : ∀ r : ℝ, r ^ (1/2) = real.sqrt r := sorry,
    rw h₀ at h,
    sorry,
  end⟩
   
/-
(dist_eq : ∀ x y, dist x y = norm (x - y))
-/

noncomputable 
instance euclidean_normed_group : normed_group (vectr s) 
  :=
  ⟨
    begin
      intros,
      dsimp only [has_norm.norm, norm_coord],
      sorry
    end
  ⟩
/-
(norm_smul_le : ∀ (a:α) (b:β), ∥a • b∥ ≤ ∥a∥ * ∥b∥)
-/

noncomputable 
instance euclidean_normed_space [module K (vectr s)] : normed_space K (vectr s) 
  :=
  ⟨begin
    intros,
    dsimp only [has_norm.norm, norm_coord],
    sorry,
  end⟩

/-
class inner_product_space (𝕜 : Type*) (E : Type*) [is_R_or_C 𝕜]
  extends normed_group E, normed_space 𝕜 E, has_inner 𝕜 E :=
(norm_sq_eq_inner : ∀ (x : E), ∥x∥^2 = re (inner x x))
(conj_sym  : ∀ x y, conj (inner y x) = inner x y)
(nonneg_im : ∀ x, im (inner x x) = 0)
(add_left  : ∀ x y z, inner (x + y) z = inner x z + inner y z)
(smul_left : ∀ x y r, inner (r • x) y = (conj r) * inner x y)

-/

instance euclidean_has_scalar : has_scalar ℝ (vectr s)
  := ⟨sorry⟩

instance euclidean_mul_action : mul_action ℝ (vectr s)
  := ⟨sorry, sorry⟩

instance euclidean_distrib_mul_action : distrib_mul_action ℝ (vectr s)
  := ⟨sorry, sorry⟩

instance euclidean_module : module ℝ (vectr s)
  := ⟨sorry, sorry⟩

noncomputable
instance euclidean_normed_space_vec : normed_space ℝ (vectr s)
  := ⟨sorry⟩

noncomputable
instance euclidean_inner_product_space : inner_product_space ℝ (vectr s)
  := ⟨sorry, sorry, sorry, sorry⟩



structure affine_euclidean_space.angle 
  :=
  (val : ℝ)



noncomputable
def vectr.compute_angle
    (v1 : vectr s)
    : vectr s → affine_euclidean_space.angle
    := 
      λ v2,
      ⟨real.arccos ⟪v1,v2⟫/∥v1∥*∥v2∥⟩


structure orientation extends vectr_basis s := 
    (col_norm_one : ∀ i : fin dim, ∥basis_vectrs i∥ = 1)
    (col_orthogonal : ∀ i j : fin dim, i≠j → ⟪basis_vectrs i,basis_vectrs j⟫ = (0:ℝ))

/-
don't prove here *yet*
-/
def mk_orientation (ortho_vectrs : fin dim → vectr s) : orientation s :=
  ⟨⟨ortho_vectrs, sorry, sorry⟩, begin
    intros,
    simp only,
    dsimp only [has_norm.norm, norm_coord],
    have h₀ : ∀ r : ℝ, r ^ (1/2) = real.sqrt r := sorry,
    rw h₀,
    have h₁ : ∀ r : ℝ, real.sqrt r = 1 ↔ r = 1 := λ r,
      if nonneg : 0 ≤ r then begin
        intros,
        split,
        intro h,
        have h₂ : (0 : ℝ) ≤ (1 : ℝ) := begin
          have h₃ : (0 : ℝ) < 1 ∨ (0 : ℝ) = 1 := or.inl real.zero_lt_one,
          have h₄ := le_iff_lt_or_eq.2 h₃,
          exact h₄,
        end,
        have h₃ := (real.sqrt_eq_iff_mul_self_eq nonneg h₂).1 h,
        simp only [mul_one] at h₃,
        exact eq.symm h₃,
        intro h,
        rw h,
        exact real.sqrt_one,
      end
      else begin
        simp only [not_le] at nonneg,
        have h₂ : r ≤ 0 := begin
          have h₃ : r < 0 ∨ r = 0 := or.inl nonneg,
          have h₄ := le_iff_lt_or_eq.2 h₃,
          exact h₄,
        end,
        intros,
        split,
        intro h,
        have h₃ := eq.trans (eq.symm (real.sqrt_eq_zero_of_nonpos h₂)) h,
        have h₄ := zero_ne_one h₃,
        contradiction,
        intro h,
        rw h at nonneg,
        have h₃ := lt_asymm real.zero_lt_one,
        contradiction,
      end,
    rw h₁,
    sorry,
  end, begin
    intros i j h,
    simp only,
    dsimp only [has_inner.inner, dot_product_coord],
    sorry,
  end⟩

structure rotation extends fm_tr s s :=
  (rotation_no_displacement : ∀ v : vectr s, ∥(to_fm_tr.transform_vectr 0)∥ = 0)
  (rotation_no_scaling : ∀ v : vectr s, ∥(to_fm_tr.transform_vectr v)∥ = 1) 
  (rotation_col_orthogonal : ∀ i j : fin dim, 
        i≠j →
        ⟪ to_fm_tr.transform_vectr (⟨(fm.base dim id_vec).basis.basis_vecs i⟩:vectr s),
          to_fm_tr.transform_vectr ((⟨(fm.base dim id_vec).basis.basis_vecs j⟩):vectr s)⟫ 
          = (0:ℝ))


def mk_rotation' {K : Type u} [inhabited K] [normed_field K] [has_lift_t K ℝ]
{dim : nat} {id_vec : fin dim → nat }{f : fm K dim id_vec} {s : spc K f} (b : vectr_basis s) : rotation s :=
⟨ 
  begin
    
    eapply fm_tr.mk,
    split,
    {
      intros,
      dsimp only [has_vadd.vadd, add_vectr_point, aff_vec_group_action, add_vec_pt, mk_point'],
      sorry
    },
    split,
    {
      dsimp only [function.left_inverse],
      intros,
      sorry
    },
    {
      dsimp only [function.right_inverse, function.left_inverse],
      intros,
      sorry
    },
    exact (λ p, mk_point_from_coords (b.to_matrix.mul_vec p.to_coords)),
    exact (λ p, mk_point_from_coords (b.to_matrix.cramer_inverse.mul_vec p.to_coords)),

         --(λ p, mk_point_from_coords (b.to_matrix.mul_vec p.to_coords)),
          --(λ p, mk_point_from_coords ((b.to_matrix.cramer_inverse.mul_vec p.to_coords)),
    split,
    {
      intros,
      sorry
    },
    {
      intros,
      sorry,
    },
    {
      dsimp only [function.left_inverse],
      intros,
      sorry
    },
    {
      dsimp only [function.right_inverse, function.left_inverse],
      intros,
      sorry
    },
    exact (λ v, mk_vectr_from_coords (b.to_matrix.mul_vec v.to_coords)),
    exact (λ p, mk_vectr_from_coords (b.to_matrix.cramer_inverse.mul_vec p.to_coords)),
  end
,begin
  intro h,
  dsimp only [fm_tr.transform_vectr],
  simp only [mk_vec, mk_pt, equiv.coe_fn_mk, norm_eq_zero],
  dsimp only [has_zero.zero],
  dsimp only [vectr_zero, mk_vectr, mk_vec_n, mk_vec],
  simp only,
  sorry,
end, sorry, sorry⟩

def mk_rotation (ortho_vectrs : fin dim → vectr s) : rotation s :=
  (mk_rotation' ⟨ortho_vectrs, sorry, sorry⟩)


instance : has_lift_t (orientation s) (rotation s) := ⟨λo, mk_rotation' o.1/-subtype notation-/⟩