import data.set   -- operations on sets

/-
Three kinds of coercions.

1. term to term: from values of one type or polymorphic family 
of types to another, e.g., ℕ → ℤ, list α → set α, allowing one to 
view of a value of one type as a value of another type
2. term to type: from a family of types to the class of sorts, 
allowing one to view any value of one term as another type
(e.g., allowing a term representing a subgroup to be promoted
to a the group type)
3. from a family of types to the class of function types,
allowing one to view any value of one type as a function 
-/


/- 1. type to type

We define a coercion from α to β by declaring an instance 
of the typeclass, has_coe α β. 

class has_coe (a : Sort u) (b : Sort v) : Sort (max (max 1 u) v) :=
(coe : a → b)
-/

-- Example: list to set coercion

-- list to set function
def list.to_set {α : Type*} : list α → set α
| []     := ∅
| (h::t) := {h} ∪ list.to_set t

-- has_coe instance on (list α) (set α) using function
instance list_to_set_coe (α : Type*) :
  has_coe (list α) (set α) :=
⟨list.to_set⟩

-- coercion in action
def set_123 : set ℕ := [1,2,3]    -- implicit coercion
def set_123' : set ℕ := ↑[1,2,3]  -- explicit coercion

-- the lift operator, ↑t, is notation for coe t

/-
The standard library defines a coercion from subtype 
{x : α // p x} to α as

instance coe_subtype {α : Type*} {p : α → Prop} :
  has_coe {x // p x} α :=
⟨λ s, subtype.val s⟩

A subtype of a type α in turn is a type whose values
are from α satisfying some predicate, p.
-/

--variables (X : Type) (p : X → Prop) (s : subtype p) -- {x : X // p x}
--#check (s : X) -- ↑s : X



def X := nat
def p : ℕ → Prop := λ n, n = 1 ∨ n = 2
abbreviation st := subtype p
def i : st := ⟨1, begin left, exact rfl end⟩
#check (↑i : ℕ⟩ 


-- subtype of ℕ containing just 1, 2, 3
abbreviation nat_123 : Type := { n : ℕ // n = 1 ∨ n = 2 ∨ n = 3} -- def defs different type!
variable xxx : nat_123
def a_nat_123 : nat_123 := ⟨1, begin left, exact rfl end⟩ 
def fn (n :ℕ) := n
#eval fn a_nat_123


def nat_1 : ℕ := (↑a_nat_123 : nat)

/-
⇑f and ↥S are notations for coe_fn f and coe_sort S. 
They are the coercion operators for the function and 
sort classes.
-/

#check @coe