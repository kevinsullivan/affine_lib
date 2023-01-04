import algebra.module.basic
import linear_algebra.affine_space.affine_equiv
import algebra.direct_sum.basic
import algebra.direct_sum.module
import tactic.linarith
import .lin2kcoord

open_locale direct_sum
/-
⨁ i, β i is now available as the n-ary direct sum.
 -/

universes u 

-- Let K be any non-empty field
variables 
  (K : Type u)  -- scalar type
  [inhabited K] -- non-empty
  [field K]     -- forms a field

-- Let n by a positive integer dimension
  (n : ℕ)       -- dimension 
  (ng1 : n > 1) -- dim is > 1

/-
Abbreviation for the type of the direct sum (think
product) of n K × K modules. The variable i here is
the index, selected from a finite set (fin) of size n.

lin2k_sum : 
  Π (K : Type u_1) 
  [_inst_1 : inhabited K] 
  [_inst_2 : field K], 
  ℕ → 
  Type u_1
-/
abbreviation lin2k_sum := ⨁(i : fin n), (λi, K × K) i

/-
Proof (by typeclass instantiation) that such a direct
sum of K×K modules over K is also a module.
-/
instance : module K (lin2k_sum K n) := by apply_instance

/-
Lean mathlib background:
https://github.com/leanprover-community/mathlib/blob/6d0adfa76594f304b4650d098273d4366edeb61b/src/algebra/direct_sum/module.lean#L52
The type, fin n, is the type, { i : ℕ, i < n}.
The type, finset α, is the type of finite sets of α's.
The type, finset (fin n), is thus the type of finite sets ℕ's less than n.

We will need a finset containing all of the elements of fin n.
We need a finset to take advantage of Lean support for finite
sums and products over types.Finsets give a basic foundation 
for defining finite sums and products over types:

    ∑ i in (s : finset α), f i;
    ∏ i in (s : finset α), f i.

Lean refers to these operations as big_operators. 
More can be found in algebra.big_operators.basic.

Finsets are directly used to define fintypes in Lean. 
A fintype α instance for a type α consists of a 
universal finset α containing every term of α, 
called univ. See data.fintype.basic
-/

def finsetn : finset (fin n) := finset.univ 

#check @finset.univ
#check finsetn
#check finsetn 5

/-
Given a mapping from i = [0,..,n-1] to 2D K-vectors, 
construct their direct sum, ⨁(i : fin n), (λi, K × K) i,
abbreviated here as lin2k_sum K n.
-/

def x := (↑(finsetn n) : set (fin n))

def mk_linnk : (fin n → K × K) → lin2k_sum K n :=
/-
Given an n-tuple of 2D K-vectors
-/
λv, 
  /-
  What is val? Given i as a subset of indices 0..n,
  -/
  let val : Π (i : (↑(finsetn n) : set (fin n))), (λi, K × K) i.val := 
  /-
  val is the function that takes 
  -/
    λi, v i in 
      -- Create direct sum of a family M of R modules indexed over ι.
      direct_sum.lmk K _ _ _ val


/-
-/
def mk_linnk : (fin n → K × K) → lin2k_sum K n :=
λv, 
  /-
  What is val? Given i as a subset of indices 0..n,
  -/
  let val : Π (i : (↑(finsetn n) : set (fin n))), (λi, K × K) i.val := 
  /-
  val is the function that takes 
  -/
    λi, v i in 
      -- Create direct sum of a family M of R modules indexed over ι.
      direct_sum.lmk K _ _ _ val

/-
def direct_sum.lmk 
  (R : Type u) [semiring R] 
  (ι : Type v) [dec_ι : decidable_eq ι] 
  (M : ι → Type w) [Π (i : ι), add_comm_monoid (M i)] [Π (i : ι), module R (M i)] 
  (s : finset ι) :
  (Π (i : ↥↑s), M i.val) →ₗ[R] direct_sum ι (λ (i : ι), M i)
-/



def mk_linnk' : (fin n → K × K) → lin2k_sum K n :=
λv, 
  let val : 
    Π (i : (↑(finsetn n) : set (fin n))), (λi, K × K) i.val := 
      λi, v i in
        direct_sum.lmk K _ _ _ val