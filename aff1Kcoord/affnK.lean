import ..lin2Kcoord.lin2kcoord
import linear_algebra.affine_space.affine_equiv
import tactic.linarith

universes u 
variables 
(K : Type u) 
[field K]
[inhabited K]

open_locale affine


-- 1-D *affine* K pt and vec objects rep'd by 2-D linear K tuples
@[ext]
structure pt extends K × K := (inv : fst = 1)
@[simp]
def mk_pt' (p : K × K) (i : p.1 = 1): pt K := @pt.mk K _ _ p i    -- private
@[simp]
def mk_pt (k : K) : pt K  := @pt.mk K _ _ (1, k) rfl              -- exported

def pt_coord (p : pt K) : K := p.to_prod.2


@[ext]
structure vec extends K × K := (inv : fst = 0)
@[simp]
def mk_vec' (p : K × K) (i : p.1 = 0): vec K := @vec.mk K _ _ p i -- private
@[simp]
def mk_vec (k : K) : vec K := @vec.mk K _ _ (0, k) rfl            -- exported

def vec_coord (v : vec K) : K := v.to_prod.2


