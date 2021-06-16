import data.real.basic
import .affnK


-- Operations on vectors using vec type
noncomputable def v1 : vec ℝ := mk_vec ℝ 0
noncomputable def v2 : vec ℝ := mk_vec ℝ 3
noncomputable def v3 := v1 + v2
noncomputable def v4 := (2 : ℝ) • v3

-- Operations involving points using pt type 
noncomputable def p1 : pt ℝ := mk_pt ℝ 0
noncomputable def p2 : pt ℝ := mk_pt ℝ 3
noncomputable def p3 := p1 -ᵥ p2
noncomputable def p4 := v4 +ᵥ p2

-- get coordinate of pt
noncomputable def p4c : ℝ := pt_coord ℝ p4


/-
-/



/-
Build an n-D affine space from n 1-D spaces
-/
abbreviation affnK (n : nat) := fin n → (affine_space (vec K) (pt K)) 





/-
-/
example : nat := 3

def a1k : affnK ℚ 1 := λ i, by apply_instance
def a2k : affnK ℚ 2 := λ i, by apply_instance
def a3k : affnK ℚ 3 := λ i, by apply_instance

#check a1k
#check a2k
#check a3k


def foo {n1 n2 : nat} (a1 : affnK K n1) (a2 : affnK K n2) : affnK K (n1 + n2) := 
  λ i : fin (n1 + n2), if i.val < n1 then a1 ⟨ i.1, sorry ⟩ else a2 ⟨ i.1 - n1, sorry ⟩ 

def a5k := foo ℚ (a2k) (a3k)

#check (a5k)

def a10k := foo ℚ (a5k) (a5k)
#check a10k 





