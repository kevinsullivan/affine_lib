import tactic.ext linear_algebra.affine_space.basic
import algebra.module linear_algebra.basis

universes u v w
variables (X : Type u) (K : Type v) (V : Type w) (ι : Type*)
[ring K] [add_comm_group V] [module K V]

variables (s : finset ι) (g : ι → K) (v : ι → V) [is_basis K v] [affine_space V X]

open_locale big_operators

-- barycenters and barycentric coordinates: here for the future
-- TODO: move this stuff to a separate file barycenters.lean or something
def affine_combination (g_add : ∑ i in s, g i = 1) := ∑ i in s, g i • v i
def barycenter (g_add : ∑ i in s, g i = 1) := g -- TODO: want to coerce g to be a list?



/-
Up to this point, we've shown that <aff_pt, aff_vec> constitutes an 
affine n-space.There's no notion of a frame at this point. However, 
we can endow such a space with a standard frame, taking the point,
<1, 0, ..., 0> as the standard origin and the vectors, <0, 1, 0, ...>,
..., <0, 0, ..., 1> as the standard basis for the vector space. To 
this end, we now define what it means to be a frame for an affine space
and we provide a function for obtaining a standard basis for any given
space of this kind.
-/

structure affine_frame :=
(ref_pt : X)
(vec : ι → V)
(basis : is_basis K vec)

/-
inductive affine_frame --need proof that "standard" is THE standard basis?
| standard (ref_pt : X) (vec : ι → V) (basis : is_basis K vec ) : affine_frame
| derived (ref_pt : X) (vec : ι → V) (basis :  is_basis K vec ) : affine_frame → affine_frame
-/

namespace aff_fr

/-
(1) Can we equip the bare affine space with a standard frame
(2) Then view a new frame as an isomorphism between spaces

Assume you're given "standard" real affine 3-space. And suppose
that conceptually you want a new coordinatizion of that space.
So you define a new origin point, P, and new vectors, V_i, in
that standard space. And from the P and the V_i you now create 
a new frame, but you do by creating a new *coordinate* space,
and one that by construction comes with an isomorphic mapping
to the original standard space.
-/

@[ext]
structure vec_with_frame (frame : affine_frame X K V ι) :=
(vec : V)

@[ext]
structure pt_with_frame (frame : affine_frame X K V ι) :=
(pt : X)


variables (basis : affine_frame X K V ι) (pt : X)

def vecf_add : vec_with_frame X K V ι basis → vec_with_frame X K V ι basis → vec_with_frame X K V ι basis :=
λ x y, ⟨x.1 + y.1⟩

def vecf_neg : vec_with_frame X K V ι basis → vec_with_frame X K V ι basis :=
λ x, ⟨-x.1⟩

def vecf_scalar : K → vec_with_frame X K V ι basis → vec_with_frame X K V ι basis :=
λ c x, ⟨c • x.1⟩

instance : has_add (vec_with_frame X K V ι basis) := ⟨vecf_add X K V ι basis⟩

instance : has_neg (vec_with_frame X K V ι basis) := ⟨vecf_neg X K V ι basis⟩

instance vec_has_zero : has_zero V := by refine add_monoid.to_has_zero V

def vecf_zero : vec_with_frame X K V ι basis := ⟨(aff_fr.vec_has_zero V).zero⟩

instance : has_zero (vec_with_frame X K V ι basis) := ⟨vecf_zero X K V ι basis⟩

instance : has_scalar K (vec_with_frame X K V ι basis) := ⟨vecf_scalar X K V ι basis⟩

#print add_comm_group

lemma vadd_assoc : ∀ x y z : vec_with_frame X K V ι basis, x + y + z = x + (y + z) := 
begin
intros,
cases x, cases y, cases z,
ext,
exact add_assoc x y z,
end

lemma vzero_add : ∀ x : vec_with_frame X K V ι basis, 0 + x = x :=
begin
intros,
cases x,
ext,
exact zero_add x,
end

lemma vadd_zero : ∀ x : vec_with_frame X K V ι basis, x + 0 = x :=
begin
intros,
cases x,
ext,
exact add_zero x,
end

lemma vadd_left_neg : ∀ x : vec_with_frame X K V ι basis, -x + x = 0 :=
begin
intros,
cases x,
ext,
exact add_left_neg x,
end

lemma vadd_comm : ∀ x y : vec_with_frame X K V ι basis, x + y = y + x := 
begin
intros,
cases x, cases y,
ext,
exact add_comm x y,
end

instance : add_comm_group (vec_with_frame X K V ι basis) :=
⟨
  vecf_add X K V ι basis, 
  vadd_assoc X K V ι basis, 
  vecf_zero X K V ι basis, 
  vzero_add X K V ι basis, 
  vadd_zero X K V ι basis, 
  vecf_neg X K V ι basis,
  vadd_left_neg X K V ι basis,
  vadd_comm X K V ι basis
⟩

#print vector_space
#print semimodule

instance : module K (vec_with_frame X K V ι basis) := sorry

instance : affine_space (vec_with_frame X K V ι basis) (pt_with_frame X K V ι basis) := sorry

end aff_fr