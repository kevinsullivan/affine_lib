import algebra.module.basic
import linear_algebra.affine_space.affine_equiv
import algebra.direct_sum.basic
import algebra.direct_sum.module
import tactic.linarith
import .lin2kcoord

open_locale direct_sum
/-
⨁ i, β i is now available as the n-ary direct sum
of objects of type β i, indexed by the values of i,
an index set.
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

/-
We need a complete subset of the finite set of 
values, m : ℕ such that m is less than n. The
function, finset_fin_N, gives us what we need.
Given n as an argument, it returns the subset 
containing the full range of values, 0..n-1, of
fin n. The value needed is finset.univ (mathlib). 
-/

def finset_fin_N : finset (fin n) := finset.univ 

/-
Given 2D modules over K indexed by i = [0,..,n-1], 
return the direct sum, ⨁(i : fin n), (λi, K × K) i.
We abbreviate this function as lin2k_sum K n.
-/

/-
We need a function set_fin_N that takes a natural
number and returns a complete set of the finite
natural numbers in the range [0,n-1]. 
-/
def set_fin_N := ( ((finset_fin_N n)) : set (fin n) )
#check set_fin_N
#reduce set_fin_N 2

def mk_linnk : (fin n → K × K) → lin2k_sum K n :=
/-
Given an n-tuple of 2D K-vectors
-/
λv, 
  /-
  What is val? Given i of type subset of finite
  indices, 0..n, of type ℕ.
  
      return type is a function that takes i
      and returns v i, where i is a complete
      finite set 0..n-1 of ℕ,
      a function  
      -/
  let val : 
      Π (i :  -- function that takes i of type complete set 0..n-1
          (↑(finset_fin_N n) : set (fin n))
        ),    
        (   -- returns the result of applying 
          λ j, K × K  
        )   
         i.val 
         -- subtype.val : Π {α : Type} {p : α → Prop}, subtype p → α
                := 
      λ i, v i 
  /-
  val is the function that takes 
  -/
    in 
      -- Create direct sum of a family M of R modules indexed over ι.
    direct_sum.lmk K _ _ _ val

#check @subtype.val


-- def mk_linnk : (fin n → K × K) → lin2k_sum K n :=
-- λv, 
--   /-
--   What is val? Given i as a subset of indices 0..n,
--   -/
--   let val : Π (i : (↑(finset_fin_N n) : set (fin n))), (λi, K × K) i.val := 
--   /-
--   val is the function that takes 
--   -/
--     λi, v i in 
--       -- Create direct sum of a family M of R modules indexed over ι.
--       direct_sum.lmk K _ _ _ val

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
    Π (i : (↑(finset_fin_N n) : set (fin n))), (λi, K × K) i.val := 
      λi, v i in
        direct_sum.lmk K _ _ _ val