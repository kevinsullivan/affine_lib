import .affine_coordinate_framed_space_lib
import .affine_coordinate_transform
import linear_algebra.affine_space.basic
import topology.metric_space.emetric_space
import analysis.normed_space.inner_product
import data.complex.is_R_or_C
import topology.metric_space.pi_Lp
import analysis.special_functions.trigonometric

universes u v w
open aff_fr aff_lib
open_locale big_operators affine
set_option class.instance_max_depth 1000

variables 
  (K : Type u) 
  [inhabited K] 
  [is_R_or_C K]
  [field K] 
  (n : ℕ) 
  (fr : affine_coord_frame K n)

namespace euclidean

--#check (∑ (i : fin n), (coords1.nth i) * (coords2.nth i))

def dot_product
  {K : Type u} 
  [field K] 
  [inhabited K] 
 -- [is_R_or_C K]
  {n : ℕ} 
  {fr : affine_coord_frame K n} 
  : aff_coord_vec K n fr → aff_coord_vec K n fr → K 
| v1 v2 := 
  let coords1 := aff_lib.affine_coord_vec.get_coords v1 in
  let coords2 := aff_lib.affine_coord_vec.get_coords v2 in
    (1 : K)--(∑ (i : fin n), (coords1.nth i) * (coords2.nth i)) ^ 2


def norm
  {K : Type u} 
  [field K] 
  [inhabited K] 
--  [is_R_or_C K]
  {n : ℕ} 
  {fr : affine_coord_frame K n} 
  : aff_coord_vec K n fr → ℝ  
| v1  := 
  let coords1 := aff_lib.affine_coord_vec.get_coords v1 in
  --let coords2 := aff_lib.affine_coord_vec.get_coords v2 in
   1 --(∑ (i : fin n), (coords1.nth i) * (coords2.nth i)) ^ 2

instance aff_coord_vec_norm : has_norm (aff_coord_vec K n fr) := ⟨norm⟩

instance aff_coord_vec_inner : has_inner K (aff_coord_vec K n fr) := ⟨dot_product⟩

notation `⟪`x`, `y`⟫` := dot_product x y

def one11 : ℝ := 1

#check 1

--instance module 
noncomputable
def l2_metric
  {K : Type u} 
  [field K] 
  [inhabited K] 
  [is_R_or_C K]
  {n : ℕ} 
  {fr : affine_coord_frame K n} 
  : aff_coord_pt K n fr → aff_coord_pt K n fr → ℝ 
| pt1 pt2 := 1

noncomputable
def l2_extended_metric
  {K : Type u} 
  [field K] 
  [inhabited K] 
  [is_R_or_C K]
  {n : ℕ} 
  {fr : affine_coord_frame K n} 
  : aff_coord_pt K n fr → aff_coord_pt K n fr → ennreal
| pt1 pt2 := 1

noncomputable
instance euclidean_distance : has_dist (aff_coord_pt K n fr) := ⟨l2_metric⟩ 

noncomputable
instance euclidean_extended_distance : has_edist (aff_coord_pt K n fr) := ⟨l2_extended_metric⟩

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
instance euclidean_metric_space_pt : metric_space (aff_coord_pt K n fr)
  :=
  ⟨
    sorry,
    sorry,
    sorry,
    sorry,
    sorry,
    sorry,
    sorry,
    sorry
  ⟩

instance euclidean_metric_space_vec : metric_space (aff_coord_vec K n fr)
  :=
  sorry
  /-⟨
    sorry,
    sorry,
    sorry,
    sorry,
    sorry,
    sorry,
    sorry,
    sorry
  ⟩-/


noncomputable
instance euclidean_extended_metric_space_pt : emetric_space (aff_coord_pt K n fr) 
  :=
  ⟨
    sorry,
    sorry,
    sorry,
    sorry,
    sorry,
    sorry
  ⟩

noncomputable
instance euclidean_extended_metric_space_vec : emetric_space (aff_coord_vec K n fr) 
  :=
  ⟨
    sorry,
    sorry,
    sorry,
    sorry,
    sorry,
    sorry
  ⟩


noncomputable
instance euclidean_extended_metric_space : emetric_space (aff_coord_pt K n fr) 
  :=
  ⟨
    sorry,
    sorry,
    sorry,
    sorry,
    sorry,
    sorry
  ⟩
   
/-
(dist_eq : ∀ x y, dist x y = norm (x - y))
-/

noncomputable 
instance euclidean_normed_group : normed_group (aff_coord_vec K n fr) 
  :=
  ⟨
    sorry
  ⟩
/-
(norm_smul_le : ∀ (a:α) (b:β), ∥a • b∥ ≤ ∥a∥ * ∥b∥)
-/
--instance vec_semimodule : semimodule K (aff_coord_vec K n fr) := sorry

noncomputable 
instance euclidean_normed_space [semimodule K (aff_coord_vec K n fr)] : normed_space K (aff_coord_vec K n fr) 
  :=
  ⟨
    sorry 
  ⟩ 

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
instance euclidean_inner_product_space : inner_product_space K (aff_coord_vec K n fr)
  := sorry
  /-maximum class-instance resolution depth has been reached 
  (the limit can be increased by setting option 'class.instance_max_depth') 
  (the class-instance resolution trace can be visualized by setting option 
  'trace.class_instances')-/
  /-⟨ 
    sorry,
    sorry,
    sorry,
    sorry,
    sorry
  ⟩ -/



--affine_space (aff_coord_vec K n fr) (aff_coord_pt K n fr)
structure affine_euclidean_space 
  [ring K] 
  [add_comm_group (aff_coord_vec K n fr)] 
  [affine_space (aff_coord_vec K n fr) (aff_coord_pt K n fr)]
  [emetric_space (aff_coord_pt K n fr)]
  [inner_product_space K (aff_coord_vec K n fr)]
  := mk ::
  --[module K (aff_coord_vec K n fr)] --WHY DOES THIS NEED TO BE HERE? ONLY IF [is_R_or_C K] IS INCLUDED?!
  --extends affine_space_type 
  --      (aff_coord_pt K n fr)
  --      K
  --      (aff_coord_vec K n fr)

noncomputable
abbreviation affine_euclidean_space.standard_space
    --[module K (aff_coord_vec K n (affine_coord_frame.standard K n))]--WHY DOES THIS NEED TO BE HERE? ONLY IF [is_R_or_C K] IS INCLUDED?!
    := affine_euclidean_space K n (affine_coord_frame.standard K n)
    --:= ⟨ ⟩ 
    
    --affine_euclidean_space K n (affine_coord_frame.standard K n)
attribute [reducible]
noncomputable
def affine_euclidean_space.mk_with_standard
    : affine_euclidean_space.standard_space K n
    := ⟨⟩


structure affine_euclidean_space.angle 
  :=
  (val : ℝ)--change this to a properly constrained quotient type of ℝ 

noncomputable
def real_affine_coord_vec.compute_angle
    {n : ℕ} 
    {fr : affine_coord_frame ℝ n} 
    (v1 : aff_coord_vec ℝ n fr)
    (v2 : aff_coord_vec ℝ n fr)
    --[has_inner K (aff_coord_vec K n fr)]
    : affine_euclidean_space.angle
    := 
      ⟨real.arccos ⟪v1,v2⟫/∥v1∥*∥v2∥⟩

end euclidean