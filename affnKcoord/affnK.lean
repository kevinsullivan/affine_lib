import ..aff1Kcoord.aff1K
import linear_algebra.affine_space.affine_equiv
import tactic.linarith

universes u 
variables 
(K : Type u) 
[field K]
[inhabited K]
(n : ℕ)

open_locale affine


abbreviation pt_n := fin n → pt K
abbreviation vec_n := fin n → vec K

def mk_pt_n (vals : vector K n) : pt_n K n := 
  λi, mk_pt K (vals.nth i)

def mk_vec_n (vals : vector K n) : vec_n K n := 
  λi, mk_vec K (vals.nth i)

def pt_n.coords {K : Type u}
[field K]
[inhabited K]
{n : ℕ} (ptn : pt_n K n) : fin n → K :=
  λi, (ptn i).coord
def vec_n.coords {K : Type u}
[field K]
[inhabited K]
{n : ℕ} (vecn : vec_n K n) : fin n → K :=
  λi, (vecn i).coord


def mk_pt_prod {n1 : ℕ} (p1 : pt_n K n1) {n2 : ℕ} (p2 : pt_n K n2) : pt_n K (n1+n2) := 
  λi, if i.1<n1 then p1 ⟨i.1,sorry⟩ else p2 ⟨i.1-n1,sorry⟩

def mk_vec_prod {n1 : ℕ} (p1 : pt_n K n1) {n2 : ℕ} (p2 : pt_n K n2) : pt_n K (n1+n2) := 
  λi, if i.1<n1 then p1 ⟨i.1,sorry⟩ else p2 ⟨i.1-n1,sorry⟩

def add_maps {n1 n2 : ℕ} {T : Type u} (m1 : fin n1 → T) (m2 : fin n2 → T) : (fin (n1 + n2) → T) := 
  λi, if i.1 < n1 then m1 ⟨i.1,sorry⟩ else m2 ⟨i.1-n1,sorry⟩


--done
instance : add_comm_group (vec_n K n) := by apply_instance
instance : affine_space (vec_n K n) (pt_n K n) := by apply_instance

