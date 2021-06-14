import .aff1K
import linear_algebra.affine_space.affine_equiv
import .aff1Kcoord

universes u 
variables 
(K : Type u) 
(n : ℕ)
[field K]
[inhabited K]
(k : ℕ)

open_locale affine

abbreviation pt_n := fin n → pt K
abbreviation vec_n := fin n → vec K

--done
instance : affine_space (vec_n K n) (pt_n K n) := by apply_instance

inductive fm_n : nat → Type u
| base : Π k, fm_n k
| deriv 
  {k : ℕ} 
  (origin : pt_n K n) 
  (basis : fin n → vec_n K n)
  (parent : fm_n k) : fm_n k 


--structure spc {n : nat} (f : fm K n) : Type u       -- interesting specimen, here, btw

structure spc_n {k : ℕ} (f : fm_n K n k) : Type u


--attempt a : works fine
structure point_n {f : fm_n K n k} (s : spc_n K n f) : Type u :=
  (coords : pt_n K n)

structure vectr_n {f : fm_n K n k} (s : spc_n K n f) : Type u :=
  (coords : vec_n K n)

--attempt b: problematic - frame is not accurate
variables (f_ : fm K n) (sp_ : spc K f_)
abbreviation other_pt_n := fin n → vectr sp_
abbreviation other_vectr_n := fin n → vectr sp_


--extends pt K cannot extend anymore
--extends vec K

/-
inductive fm : nat → Type u
| base : Π n, fm n
| deriv : Π n, (prod (pt K) (vec K)) → fm n → fm n  -- TODO: curry all of these args
-/