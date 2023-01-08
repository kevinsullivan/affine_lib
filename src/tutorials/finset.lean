import algebra.direct_sum.module

-- finset: Defines a type for the finite subsets of α. Constructing a finset requires two pieces of data: val, a multiset α of elements, and nodup, a proof that val has no duplicates.

#check finset ℕ 

def empty_fs : finset ℕ := finset.empty
def singleton_fs : finset ℕ := { 0 }
def range_fs : finset ℕ := finset.range 2 -- [0,..,1]
def fs_from_subtype : finset { r : ℕ | r ∈ range_fs } := finset.attach range_fs

-- finset.has_mem: Defines membership a ∈ (s : finset α).

example : 0 ∈ range_fs := sorry


-- finset.has_coe: Provides a coercion s : finset α to s : set α.
-- recall: a set in Lean is represented by its membership predicate 
-- KS: it's has_coe_t; it's still applied by the lift operator, ↑.
def set_from_fs : set ℕ := ↑range_fs
#reduce set_from_fs

/-
finset.has_coe_to_sort: Coerce s : finset α to the type of all x ∈ s.
https://leanprover.github.io/theorem_proving_in_lean/type_classes.html
https://leanprover-community.github.io/mathlib_docs/data/subtype.html

notation `↑`:max x:max := coe x
notation `⇑`:max x:max := coe_fn x
notation `↥`:max x:max := coe_sort x
-/

#check {n : ℕ // n ∈ range_fs}    -- subtype (//) of ℕ in range_fs 
#reduce {n : ℕ // n ∈ range_fs}   -- expanding membership predicate

def sort_from_fs : Type := @has_coe_to_sort range_fs {n : ℕ // n ∈ range_fs} 
#reduce sort_from_fs
example : sort_from_fs := _ 
-- KS: hmm, instantiate one; ⟨,⟩ doesn't work



-- finset.induction_on: 

/-
Induction on finsets. To prove a proposition about an 
arbitrary finset α, it suffices to prove it for the empty
finset, and to show that if it holds for some finset α, 
then it holds for ANY finset obtained by inserting any 
new element into it.
-/



/- finset.choose: Given a proof h of existence and uniqueness 
of aN element satisfying a predicate, choose s h returns the
element of s satisfying that predicate.
-/



/-
finsets from functions (predicates)
-/

/- 
finset.filter: Given a predicate p : α → Prop, s.filter p 
is the finset consisting of the elements in s that satisfy p.
-/
def just_zero_fs := range_fs.filter (λ v, v %2 = 0)
#check just_zero_fs  -- cool
#eval just_zero_fs
-- The data.equiv files describe a general type of equivalence, so look in there for any lemmas. There is some API for rewriting sums and products from s to t given that s ≃ t. TODO: examples

/-
Lattice structure
-/

/-
Operations on two or more finsets
-/

def range_3_fs :finset ℕ := 
  finset.cons 
    2 
    range_fs 
    begin  -- pf 2 ∉ range_fs
      assume h,
      repeat {cases h},
    end

-- KS: finset insert no longer in mathlib?

def range_3_fs' := range_fs ∪ {2}
#eval range_3_fs'

def just_1_fs := range_fs ∩ {1}
#eval just_1_fs

def just_1_fs' := range_fs.erase 0
#eval just_1_fs'
example : just_1_fs = just_1_fs' := rfl

-- finset difference is s \ t


-- finset product

def by_3_3 := range_fs × range_fs
#reduce by_3_3

/-
finset.bUnion: Finite unions of finsets; given an 
indexing function f : α → finset β and a s : finset α, 
s.bUnion f is the union of all  finsets of the form,
f a, for a ∈ s.
-/

-- contstant map, (_ : fin 2) -> range_fs 
def an_f (a : nat) := range_fs

/-
finset.bUnion : 
  Π {α : Type} 
    {β : Type u_1} [_inst_1 : decidable_eq β], 
    finset α →            -- fin nat
    (α → finset β) →      -- nar → finset β 
    finset β

-- KS: fix docs re implicit third arg, finset α
-/
def bun := range_fs.bUnion an_f
#reduce bun


/-
Maps constructed using finsets
-/

/-
finset.piecewise: Given two functions f, g, 
s.piecewise f g is a function that is equal to 
f on s and equal to g on the complement of s
(within its potentially larger element type).
-/



/-
Predicates on finsets

- disjoint
- empty

later.
-/



/-
Equivalences between finsets

The data.equiv files describe a general type of 
equivalence, so look in there for any lemmas.
-/

/-
The standard library defines a coercion from subtype 
{x : α // p x} to α as follows. 

instance coe_subtype {α : Type*} {p : α → Prop} :
  has_coe {x // p x} α := ⟨λ s, subtype.val s⟩.
-/