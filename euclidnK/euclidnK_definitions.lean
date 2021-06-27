import ..affnKcoord.affnKcoord_transforms
import data.real.basic
import linear_algebra.affine_space.basic
import topology.metric_space.emetric_space
import analysis.normed_space.inner_product
import data.complex.is_R_or_C
import topology.metric_space.pi_Lp
import data.real.nnreal

universes u

open_locale big_operators
open_locale nnreal

open ennreal

variables
{K : Type u} [field K] [inhabited K] 
  [has_lift_t K ℝ]
  [normed_field K]
{dim : nat} {id_vec : fin dim → nat }{f : fm K dim id_vec} (s : spc K f)
{dim2 : nat } {id_vec2 : fin dim → nat} {f2 : fm K dim id_vec} (s2 : spc K f2)

def dot_product_coord
  : vectr s → vectr s → ℝ
| v1 v2 := 
    (∑ (i : fin dim), ↑((v1.coords i).coord * (v1.coords i).coord))

    

def norm_coord
  : vectr s → ℝ
| v1 := 
    (∑ (i : fin dim), ↑((v1.coords i).coord * (v1.coords i).coord)) ^ (1/2)

instance vectr_norm : has_norm (vectr s) := ⟨norm_coord s⟩

instance vectr_inner : has_inner ℝ (vectr s) := ⟨dot_product_coord s⟩

notation `⟪`x`, `y`⟫` := has_inner.inner x y

noncomputable
def l2_metric
  : point s → point s → ℝ
| pt1 pt2 := ∥pt1 -ᵥ pt2∥

noncomputable
def l2_extended_metric
  : point s → point s → ennreal
| pt1 pt2 := option.some (⟨∥pt1 -ᵥ pt2∥,sorry⟩:(ℝ≥0))

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

instance euclidean_metric_space_pt : metric_space (point s)
  := sorry

instance euclidean_metric_space_vec : metric_space (vectr s)
  :=
  sorry

noncomputable
instance euclidean_extended_metric_space_pt : emetric_space (point s) 
  := sorry

noncomputable
instance euclidean_extended_metric_space_vec : emetric_space (vectr s) 
  := sorry


noncomputable
instance euclidean_extended_metric_space : emetric_space (point s) 
  := sorry
   
/-
(dist_eq : ∀ x y, dist x y = norm (x - y))
-/

noncomputable 
instance euclidean_normed_group : normed_group (vectr s) 
  :=
  ⟨
    sorry
  ⟩
/-
(norm_smul_le : ∀ (a:α) (b:β), ∥a • b∥ ≤ ∥a∥ * ∥b∥)
-/

noncomputable instance tttt : normed_field ℚ := by apply_instance

noncomputable 
instance euclidean_normed_space [module K (vectr s)] : normed_space K (vectr s) 
  :=
  sorry

/-
class inner_product_space (𝕜 : Type*) (E : Type*) [is_R_or_C 𝕜]
  extends normed_group E, normed_space 𝕜 E, has_inner 𝕜 E :=
(norm_sq_eq_inner : ∀ (x : E), ∥x∥^2 = re (inner x x))
(conj_sym  : ∀ x y, conj (inner y x) = inner x y)
(nonneg_im : ∀ x, im (inner x x) = 0)
(add_left  : ∀ x y z, inner (x + y) z = inner x z + inner y z)
(smul_left : ∀ x y r, inner (r • x) y = (conj r) * inner x y)

-/

noncomputable
instance euclidean_inner_product_space : inner_product_space ℝ (vectr s)
  := sorry



structure affine_euclidean_space.angle 
  :=
  (val : ℝ)



noncomputable
def real_affine_coord_vec.compute_angle
    (v1 : vectr s)
    (v2 : vectr s)
    : affine_euclidean_space.angle
    := 
      ⟨real.arccos ⟪v1,v2⟫/∥v1∥*∥v2∥⟩


def orientation := 
  {b : fin dim → vectr s // 
  ∀ i : fin dim, ∥b i∥ = 1 ∧ 
  ∀ i j : fin dim, i≠j → ⟪b i,b j⟫ = (0:ℝ)}

def rotation :=
  {
      tr : fm_tr s s // 
      ∀ v : vectr s, ∥(tr.transform_vectr v)∥ = 1 ∧ 
      ∀ i j : fin dim, 
        i≠j →
        ⟪ tr.transform_vectr (⟨(fm.base dim id_vec).basis i⟩:vectr s),
          tr.transform_vectr ((⟨(fm.base dim id_vec).basis j⟩):vectr s)⟫ 
          = (0:ℝ)
  }
