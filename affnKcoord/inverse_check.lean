import .affnK
import linear_algebra.affine_space.affine_equiv
import linear_algebra.matrix
import tactic.linarith

universes u 
--variables 
--(n : ℕ)

def n := 3

abbreviation K := ℚ

def mymat : matrix (fin n) (fin n) K := 
  λi, λ j, if i=j then 3 else 0

--cleanup affnk coords
--delete old comments
--
def myinv := (mymat).nonsing_inv

def mycramer := matrix.cramer_map (mymat) (λi, if i.1 = 0 then 1 else 0) ⟨0,begin 
  let : n = 3 := rfl,
  simp *,
end⟩

#eval mycramer

def mycramer2 := matrix.cramer_map (mymat) (mymat ⟨0,begin 
  let : n = 3 := rfl,
  simp *,
end⟩
) ⟨0,begin 
  let : n = 3 := rfl,
  simp *,
end⟩

#eval mycramer2


def new_mat : matrix (fin n) (fin n) K := 
  λfi fj, 
  let i := fi.1 in let j := fj.1 in
  if i = 0 ∧ j = 0 then 1 else 
  if i = 1 ∧ j = 0 then 3 else
  if i = 2 ∧ j = 0 then -1 else
  if i = 0 ∧ j = 1 then -2 else
  if i = 1 ∧ j = 1 then 5 else
  if i = 2 ∧ j = 1 then 3 else
  if i = 0 ∧ j = 2 then 3 else
  if i = 1 ∧ j = 2 then 2 else
  if i = 2 ∧ j = 2 then -4 else 0

def mycramerf := matrix.cramer_map (new_mat) (λi, new_mat i ⟨0, begin let : n = 3 := rfl, simp * end⟩)
 ⟨0,begin 
  let : n = 3 := rfl,
  simp *,
end⟩

#eval mycramerf