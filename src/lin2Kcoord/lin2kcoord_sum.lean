import algebra.module.basic
import linear_algebra.affine_space.affine_equiv
import algebra.direct_sum.basic
import algebra.direct_sum.module
import tactic.linarith
import .lin2kcoord

open_locale direct_sum
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
Next we introduce notation for the direct sum of 
a set of types with an associated module structure
(we actually require additive commutative monoids).
⨁ ι, β ι is now available notation for n-ary direct 
sum of a collection of additive commutitive monoids:
types, β i (indexed by ι), with proofs that each is 
equipped with this structure.

def direct_sum 
  (ι : Type v) 
  (β : ι → Type w) 
  [Π (i : ι), add_comm_monoid (β i)] :
  Type (max v w)

This is all from mathlib.
-/

/-
We use this function to compute direct sums of our
2-D K-vector spaces. The idea is that we'll use these
n-tuples of K × K values to represent points and vectors
in affine spaces. 

Such a function takes a natural number, n, and returns 
the direct sum (think product type), informally (K × K)ⁿ
where for each ι in the index set, the corresponding type
is constant K × K.

lin2k_sum : 
  Π (K : Type u_1) 
  [_inst_1 : inhabited K] 
  [_inst_2 : field K], 
  ℕ → 
  Type u_1

A direct product type combines a family of types indexed by ι  
-/

/-
Given a finite set of 2D modules over K, indexed 
by i = [0,..,n-1] (finite nats), return the direct 
sum, ⨁(i : fin n), (λ j, K × K) i. Read this as
the direct sum over i of a set of types indexed by
ι, where each type is just K × K. The result can
be thought of as (K × K)ⁿ, represented notationally 
as Π₀ (i : fin n), K × K.
-/

#check ⨁(i : fin n), (λ (j : fin n), K × K) i
#reduce ⨁(i : fin n), (λ (j : fin n), K × K) i
-- Π₀ (i : fin n), K × K (see this notation)

-- we define lin2k_sum K n to return this (K × K)ⁿ type
abbreviation lin2k_sum := ⨁(i : fin n), (λ j, K × K) i
-- note: for any j in i, (λ j, K × K) returns type K × K 
#check @lin2k_sum 
#reduce @lin2k_sum              -- returns Π₀ (i : fin n), K × K
#reduce lin2k_sum ℚ 3           -- direct sum of 3 copies of Q × Q 
#reduce Π₀ (i : fin 3), ℚ × ℚ   -- alternative notation, (ℚ × ℚ)³


/-
Finally, we imbuing each such  space with the structure of 
a module. This is  easy and automated in Lean, by typeclass
instantiation. A direct sum of K × K-modules with scalars of 
type K is thus proven also to be a module with scalars in K.
-/
instance : module K (lin2k_sum K n) := by apply_instance

/- 
******************************************************** 
-/

/-
Lean mathlib background:

The type, fin n, is the subtype of ℕ, { i : ℕ, i < n}. A 
value, v, of this type is a pair: a natural number, val;
and property, a proof that val < n. 

structure fin (n : ℕ) :=
(val : nat)
(property : val < n)

`finset α` is the type of finite sets of elements of `α`,
implemented as a multiset (a list up to permutation) with
no duplicate elements.   
-/
#check finset ℕ 
/-
structure finset (α : Type*) :=
(val : multiset α)
(nodup : nodup val)

The type, finset (fin n), is thus the type of 
finite sets of finite natural number values, each
in turn represented as a ℕ-value/proof pair (the
proof certifies that the value is in range).

"Finsets give a = basic foundation for defining 
finite sums and products over types:

    ∑ i in (s : finset α), f i;
    ∏ i in (s : finset α), f i.

Lean refers to these operations as big_operators. 
More can be found in algebra.big_operators.basic.

A fintype α instance consists of a "universal" 
finset α, containing every term of α. In Lean it
is called univ. See data.fintype.basic.
-/

#check fintype  -- typeclass instance
/-
fintype α means that α is finite, i.e. there are 
only finitely many distinct elements of type α. 
The evidence of this is a finset elems (a list up
to permutation without duplicates), together with 
a proof that everything of type α is in the list.
-/

/-
We now define (finset_fin_N n) as the universal
finset of finite natural numbers up to n. 
Given n as an argument, it returns the finset 
containing the full range of values, 0..n-1, of
fin n, each in turn being a pair of a ℕ and a
proof that it's in range. The term finset.univ 
(from mathlib) gives us this value. 
-/

def finset_fin_N := (finset.univ : finset (fin n) ) 
#check finset_fin_N
/-
finset_fin_N : Π (n : ℕ), finset (fin n),
where the return value is the universal finset
of value of fin n.
-/

/-
We define set_fin_N as a function that takes a
natural number, n, and returns a complete set 
of the finite natural number (value-proof pairs)
in the range [0,n-1]. 
-/


/-

-/
def set_fin_N := (((finset_fin_N n)) : set (fin n)) 

#check set_fin_N
/-
set_fin_N : Π (n : ℕ), set (fin n)
-/

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
      Π (i :  -- function that takes i, 
              -- a complete set of finite
              -- natural numbers, 0..n-1
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