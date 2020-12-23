import .list_as_k_tuple linear_algebra.affine_space.basic
import linear_algebra.basis
import .affine_coordinate_space
import data.real.basic

-- open_locale affine
/-
This file contains
affine_tuple_coord_frame
affine_coord_frame
aff_coord_pt
aff_coord_vec
Also all instances necessary. Missing some proofs 11/20
-/



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

/-
An affine frame comprises an origin point
and a basis for the vector space.
-/
structure affine_tuple_coord_frame
(K : Type w)
(n : ℕ)
[inhabited K]
[field K]  :=
mk ::
    (origin : aff_pt_coord_tuple K n) 
    (basis : (fin n) → aff_vec_coord_tuple K n) 
    (proof_is_basis : is_basis K basis) 

inductive affine_coord_frame
(K : Type w)
(n : ℕ)
[inhabited K]
[field K]
| tuple (base : affine_tuple_coord_frame K n) 
    : affine_coord_frame
| derived 
    (origin : aff_pt_coord_tuple K n) 
    (basis : (fin n) → aff_vec_coord_tuple K n) 
    (proof_is_basis : is_basis K basis) 
    (base : affine_coord_frame)
    : affine_coord_frame


structure aff_coord_pt (fr : affine_coord_frame K n) 
            extends aff_pt_coord_tuple K n :=
   -- (tuple : aff_pt_coord_tuple K n)
   mk ::

structure aff_coord_vec (fr : affine_coord_frame K n) 
            extends aff_vec_coord_tuple K n  :=
   -- (tuple : aff_vec_coord_tuple K n)
   mk ::

variables 
    (fr : affine_coord_frame K n) 
    (cv1 cv2 : aff_coord_vec K n fr) 
    (cp1 cp2 : aff_coord_pt  K n fr)

def vec_add_coord : aff_coord_vec K n fr → aff_coord_vec K n fr → aff_coord_vec K n fr :=
    λ x y, ⟨⟨ladd x.1.l y.1.l, list_sum_fixed K n x.1 y.1, sum_fst_fixed K n x.1 y.1⟩⟩
def vec_zero_coord : aff_coord_vec K n fr := ⟨⟨zero_vector K n, len_zero K n, head_zero K n⟩⟩
def vec_neg_coord : aff_coord_vec K n fr → aff_coord_vec K n fr
| ⟨⟨l, len, fst⟩⟩ := ⟨⟨vecl_neg l, vec_len_neg K n ⟨l, len, fst⟩, head_neg_0 K n ⟨l, len, fst⟩⟩⟩


/-! ### type class instances for the abelian group operations -/
instance : has_add (aff_coord_vec K n fr) := ⟨vec_add_coord K n fr⟩
instance : has_zero (aff_coord_vec K n fr) := ⟨vec_zero_coord K n fr⟩
instance : has_neg (aff_coord_vec K n fr) := ⟨vec_neg_coord K n fr⟩
@[ext]
def vec_scalar_coord : K → aff_coord_vec K n fr → aff_coord_vec K n fr :=
    λ a x, ⟨⟨scalar_mul a x.1.1, trans (scale_len a x.1.1) x.1.2, sorry⟩⟩
/-! ### Type class instance for abelian group -/
instance aff_comm_group_coord : add_comm_group (aff_coord_vec K n fr) :=
begin
    sorry
end
instance : has_scalar K (aff_coord_vec K n fr) := ⟨vec_scalar_coord K n fr⟩

lemma vec_mul_smul_coord : ∀ g h : K, ∀ x : aff_coord_vec K n fr, (g * h) • x = g • h • x := sorry


instance : mul_action K (aff_coord_vec K n fr) := ⟨sorry, vec_mul_smul_coord K n fr⟩


instance : distrib_mul_action K (aff_coord_vec K n fr) := 
    sorry
instance aff_semimod_coord : semimodule K (aff_coord_vec K n fr)
    --[distrib_mul_action K (aff_coord_vec K n fr)] 
    := 
    -- extremely odd that this doesnt work....
    ⟨sorry, sorry⟩



def aff_group_action_coord : (aff_coord_vec K n fr) → (aff_coord_pt K n fr) → (aff_coord_pt K n fr) :=
    λ x y, ⟨⟨ladd x.1.1 y.1.1, sorry, sorry⟩⟩

def aff_group_sub_coord : (aff_coord_pt K n fr) → (aff_coord_pt K n fr) → (aff_coord_vec K n fr) :=
    λ x y, ⟨⟨ladd x.1.1 (vecl_neg y.1.1), sorry, sorry⟩⟩



instance : has_vadd (aff_coord_vec K n fr) (aff_coord_pt K n fr) := ⟨aff_group_action_coord K n fr⟩

instance : has_vsub (aff_coord_vec K n fr) (aff_coord_pt K n fr) := ⟨aff_group_sub_coord K n fr⟩

instance : add_action (aff_coord_vec K n fr) (aff_coord_pt K n fr) := sorry--⟨aff_group_action K n, aff_zero_sadd K n, aff_add_sadd K n⟩

def pt_plus_vec
    {X : Type u} 
    {K : Type v} 
    {V : Type w} 
    {n : ℕ}
    {ι : Type*}
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    {fr : affine_coord_frame K n} :
    (aff_coord_pt K n fr) → 
    (aff_coord_vec K n fr) → 
    (aff_coord_pt K n fr) 
| p v := aff_group_action_coord K n fr v p

notation
 pt +ᵥ v := pt_plus_vec pt v

 
def vec_mul_scalar
    {X : Type u} 
    {K : Type v} 
    {V : Type w} 
    {n : ℕ}
    {ι : Type*}
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    {fr : affine_coord_frame K n} :
    (aff_coord_vec K n fr) → 
    K → 
    (aff_coord_vec K n fr) 
| v s := s • v

notation
 v • s := vec_mul_scalar v s
 
def pt_minus_vec
    {X : Type u} 
    {K : Type v} 
    {V : Type w} 
    {n : ℕ}
    {ι : Type*}
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    {fr : affine_coord_frame K n} :
    (aff_coord_pt K n fr) → 
    (aff_coord_vec K n fr) → 
    (aff_coord_pt K n fr) 
| p v := aff_group_action_coord K n fr (vec_neg_coord K n fr v) p

notation
 pt -ᵥ v := pt_minus_vec pt v


def prf : affine_space (aff_coord_vec K n fr) (aff_coord_pt  K n fr) := sorry

instance afc : affine_space 
    (aff_coord_vec K n fr) 
    (aff_coord_pt  K n fr) := 
    prf K n fr

end aff_fr