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
- set:      https://leanprover-community.github.io/mathlib_docs/init/data/set.html#set
- fin:      https://leanprover-community.github.io/mathlib_docs/init/data/fin/basic.html#fin
- finset:   https://leanprover-community.github.io/mathlib_docs/data/finset/basic.html
- multiset: https://leanprover-community.github.io/mathlib_docs/data/multiset/basic.html#multiset
            -- represented as quotient of a list by permutation (an unordered with duplicates possible)
-/

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

-- we define (lin2k_sum K n) to be this type, (K × K)ⁿ
-- note: ∀ j in i, (λ j, K × K) returns the type, K × K 
abbreviation lin2k_sum := ⨁(i : fin n), (λ j, K × K) i

#check @lin2k_sum 
#reduce @lin2k_sum              -- returns Π₀ (i : fin n), K × K
#reduce lin2k_sum ℚ 3           -- direct sum of 3 copies of Q × Q 
#reduce Π₀ (i : fin 3), ℚ × ℚ   -- alternative notation, (ℚ × ℚ)³

/-
mk β s x is the element of ⨁ i, β i that is zero outside s and 
has coefficient x i for i in s
-/
#check @direct_sum.mk
/-
direct_sum.mk : 
  Π {ι : Type v} [dec_ι : decidable_eq ι] 
    (β : ι → Type w) [_inst_1 : Π (i : ι), add_comm_monoid (β i)] 
    (s : finset ι), 
      (Π (i : ↥↑s), β i.val) →+ 
      ⨁ (i : ι), β i

M →+ N is the type of functions M → N that preserve the 
add_zero_class structure. add_monoid_hom is also used for group 
homomorphisms. When possible, instead of parametrizing results over 
(f : M →+ N), parametrize over (F : Type*) [add_monoid_hom_class F M N] 
(f : F).
-/

/-
Finally, we imbuing each such  space with the structure of 
a module. This is  easy and automated in Lean, by typeclass
instantiation. A direct sum of K × K-modules with scalars of 
type K is thus proven also to be a module with scalars in K.
-/
instance : module K (lin2k_sum K n) := by apply_instance

/-
How do I make a finset?
-/
def y : multiset (fin 1) := { ⟨ 0, sorry⟩ }

def x : finset (fin 1) := ⟨ y, sorry ⟩ 

-- requires a multiset of fin 1 values


def myβ := λ (i : fin 1), ℚ × ℚ
def foo : lin2k_sum ℚ 1 := 
  @direct_sum.mk 
    (fin 1)       -- index set
    _             -- cert decidable equality 
    myβ           -- indexed family of types 
    sorry             -- cert all are modules 
    x 
    _            -- finite set of indices


#check @direct_sum.mk (fin 2) _ my_β 
/-
Π [_inst_1 : Π (i : fin 2), add_comm_monoid (my_β i)] 
  (s : finset (fin 2)),
(Π (i : ↥↑s), my_β i.val) →+ ⨁ (i : fin 2), my_β i

So i here has to be an element of finset (fin 2), which
is to say a pair, ⟨val, val < n ⟩, with i.val an element
of fin 2 (see above), and my_β i.val the type, ℚ × ℚ in
this case. 

How do I make a value of type fin 2?
How do I make a value of type finset (fin 2)?
-/

example : fin 2 := ⟨ 0, by norm_num ⟩ -- good
example : fin 2 := ⟨ 1, by norm_num ⟩ -- good 
example : fin 2 := ⟨ 2, by norm_num ⟩ -- bad

/-
has_coe_t (finset α) (set α): Convert finset to set (up-arrow)
has_coe_to_sort (finset α) (Type u): Coerce finset to subtype (bar-up)
-/

/-
Move this us an explain the overall program. 

The idea is to use (n+1)-sums of these pairs as parametric
representations of a n-dimension affine points and vectors.
The approach is a slight adaptation of an otherwise standard
homogeneous coordinate representation, with the constraints 
that the first component of a representation of an affine 
vector has coordinate (0 : K), and the first component of a
representation of an affine point has coordinate (1 : K). 

For example, a 1-d affine vector, v, with coordinate tuple, 
(k), would be represented by ⟨0, k⟩ : ℚ × ℚ. An affine point, 
p, with coordinate k would be represented as ⟨1, k⟩ : ℚ × ℚ.
More generally, Lean libraries overload these angle brackets
to define structures (product types) by giving their field
values. 
-/

example : ℚ × ℚ := ⟨ 1/2, -2/3 ⟩ 

/-
It seems that if lift 1-tuples of these pairs to be 1-direct
sums, then from there we work in terms of build bigger and 
bigger direct sums. Do we need to do this? Maybe not. We do
have module structures all the way down to the bare pair, as
well as in the direct sum, spaces. Hold off on this. Think
it through.
-/

/- 
******************************************************** 
-/

/-
Lean mathlib background:

The type, fin n, is the subtype of all finite ℕ values 
less than any given ℕ, n: { i : ℕ | i < n}. A value, v, 
of this type is a pair: val, the naturan number value; 
and property, a proof certifying statically that val < n. 

structure fin (n : ℕ) :=
(val : nat)
(property : val < n)
-/


/-
The type `finset α` is the type of finite sets of values
of type `α`, implemented as a multiset, in turn a list up 
to permutation, certified as having no duplicate elements.   
-/
#check finset ℕ 
/-
structure finset (α : Type*) :=
(val : multiset α)
(nodup : nodup val)
-/

/-
The type, finset (fin n), is thus the type of 
finite sets of finite natural number values, each
in turn represented as a value/proof pair. The
proof again certifies that val < n.

Finsets provide basic foundation in Lean for 
defining finite sums and products over types:

    ∑ i in (s : finset α), f i;
    ∏ i in (s : finset α), f i.

Lean refers to these operations as big_operators. 
More can be found in algebra.big_operators.basic.

Sullivan: Using?
-/


/-
Finally fintype α is a typeclass an instance of
which consists of a universal/complete finset α 
(containing every term of α). In Lean this value
is called univ. See data.fintype.basic.
-/
#check fintype ℕ 

/-Having a fintype α instance shows α is finite:
there are only finitely many distinct elements of 
type α. The evidence of this, in turn, is a finset, 
elems (a list up to permutation without duplicates), 
together with a proof that everything of type α is 
in that list.
-/


/-
We now define finset_fin_N as a function that
takes n : ℕ, and returns the universal finset of 
finite natural numbers up to n. Recall that each 
finite natural number is turn being a pair of a 
value and proof that it's within range. The term
finset.univ (from mathlib) provides this value. 
-/

def finset_fin_N : finset (fin n) := finset.univ 
/-
finset_fin_N : Π (n : ℕ), finset (fin n),
where the return value is the universal finset
of value of fin n.
-/
#eval finset_fin_N 3  -- Lean pretty prints it

/-
We define set_fin_N as a function that takes a
natural number, n, and returns a complete set 
of the finite natural number (value-proof pairs)
in the range [0,..,n-1]. 
-/


/-
Given n, return the set of finite natural numbers
[0, n-1]. Implemented by applying finset_fin_N to
n to obtain a universal finset of finite ℕ values,
[0,..,n-1], and then coercing it to a set of such
values. Lean's mathlib provides this coercion. A
set in Lean is define by its membership predicate.
-/
def set_fin_N := (((finset_fin_N n)) : set (fin n)) 
#check @set_fin_N
/-
set_fin_N : Π (n : ℕ), set (fin n) -- complete set
-/
#reduce set_fin_N 2   -- the set membership predicate

/-
λ (x : fin 2), x = ⟨0, _⟩ ∨ x = ⟨1, _⟩ ∨ false
-/

/-
Given a function from [0,..,n-1] to K × K, which is to 
say, an tuple of K × K pairs indexed by n, return the 
the n-dimensional direct product of (K × K) spaces to
which it belongs. (This seems to be over-complicated.)
-/
/-
Type check expression used to define this function
-/
#check Π (i : set_fin_N n), ( λ j, K × K ) i.val 
/-
Π (i : ↥(set_fin_N n)), (λ (j : fin n), K × K) i.val : Type u
That is, given (set_fin_N n), return sum (K × K)ⁿ
-/
#check (Π (i : set_fin_N n), ( λ j, K × K ) i.val)
#check (set_fin_N n)
#check ↥(set_fin_N n)
#reduce  (↥(set_fin_N 2))  
/-
{x // x = ⟨0, _⟩ ∨ x = ⟨1, _⟩ ∨ false}
-/

/-
--  a function that takes i, 
-- a complete set of finite
-- natural numbers, 0..n-1,
-- and that returns K × K
-/
#check Π (i : set_fin_N n), ( λ j, K × K ) i.val 
#check (Π (i : set_fin_N n), ( λ j, K × K ) i.val) 
#check (Π (i : set_fin_N 2), ( λ j : fin 2, K × K ) i.val) 

/-
Given an indexed tuple of K × K pairs, return it as
an element of the direct sum of the K × K spaces.
-/
def mk_linnk : (fin n → K × K) → lin2k_sum K n := 
λ v, 
  /-
  Let val be a function that takes a complete set, i, 
  of finite natural numbers from [0, n-1], to the result
  of applying the constant function 
  -/
  let foo 
    : 
      Π (i : set_fin_N n),
        --  a function that takes i, 
        -- a complete set of finite
        -- natural numbers, 0..n-1,
        -- and that returns K × K
        ( λ j : fin n, K × K ) i.val 
      := 
         -- subtype.val : Π {α : Type} {p : α → Prop}, subtype p → α
         -- Given index h, return the h'th pair in v
      λ h, v h 
    in 
      -- Direct sum of a family of R modules indexed by ι.
    direct_sum.lmk K _ _ _ foo

def x : (fin 1 → ℚ × ℚ) :=
begin
assume i,
exact ⟨ 7, 7 ⟩,
end 

#check x

#check lin2k_sum K n  

#check mk_linnk ℚ 1 x    
-- this is a value of type lin2k_sum ℚ 2, but
-- it's independent of the argument value
-- in other words, this is useless and (lemma)
-- can be replaced by lin2k_sum ℚ 2 

#check ((mk_linnk ℚ 1 x) : lin2k_sum ℚ 1)
#reduce (mk_linnk ℚ 1 x) 

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
    Π (i : (↑(finset_fin_N n) : set (fin n))), (λ j , K × K) i.val := 
      λ j, v j in
        direct_sum.lmk K _ _ _ val