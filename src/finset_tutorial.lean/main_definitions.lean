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
-- KS: hmm, instantiate one 


-- finset.induction_on: Induction on finsets. To prove a proposition about an arbitrary finset α, it suffices to prove it for the empty finset, and to show that if it holds for some finset α, then it holds for the finset obtained by inserting a new element.



-- finset.choose: Given a proof h of existence and uniqueness of a certain element satisfying a predicate, choose s h returns the element of s satisfying that predicate.

/-
finsets from functions (predicates)
-/

-- finset.filter: Given a predicate p : α → Prop, s.filter p is the finset consisting of those elements in s satisfying the predicate p.

def just_zero_fs : finset ℕ := range_fs.filter (λ v, v %2 = 0)
#eval just_zero_fs  -- cool

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

def range_3_fs' := range_fs ∪ {2}
#eval range_3_fs'

def just_1_fs := range_fs ∩ {1}
#eval just_1_fs

def just_1_fs' := range_fs.erase 0
#eval just_1_fs'