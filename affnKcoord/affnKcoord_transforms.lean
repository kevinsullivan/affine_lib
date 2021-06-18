import .affnKcoord_affinespace

universes u

section implicitK

variables 
{K : Type u} [field K] [inhabited K] 
{dim : nat} {id_vec : fin dim → nat }{f : fm K dim id_vec} (s : spc K f)
{dim2 : nat } {id_vec2 : fin dim2 → nat} {f2 : fm K dim2 id_vec2} (s2 : spc K f2)

/-
Let raw_tr be the *type* of an affine equivalence
between abstract affine spaces comprising unframed
(abstract, without coordinates) points and vectors.

An affine equivalence is an equivalence, ≃ᵃ[K], 
between affine spaces such that both forward and
inverse maps are affine.

Lean defines it using an equiv for the map and a 
linear_equiv for the linear part in order to allow
affine equivalences with good definitional equalities.
-/
abbreviation raw_tr := (pt_n K dim) ≃ᵃ[K] (pt_n K dim)

/-
Structure simply encapsulating an affine transform from 
points between two affine coordinate spaces, s1 and s2.
-/
structure fm_tr 
    {f1 :  fm K dim id_vec} {f2 :  fm K dim id_vec} 
    (s1 : spc K f1) (s2 : spc K f2) extends (point s1) ≃ᵃ[K] (point s2)

/-
Inverse

KEVIN: Explain, or remove, the .1 notation here. Use identifiers when possible.
-/
def fm_tr.symm  {f1 :  fm K dim id_vec} {f2 :  fm K dim id_vec} 
    {s1 : spc K f1} {s2 : spc K f2} (ftr : fm_tr s1 s2) : fm_tr s2 s1 :=
    ⟨ftr.1.symm⟩

/-
Composition
-/
def fm_tr.trans  {f1 :  fm K dim id_vec} {f2 :  fm K dim id_vec} {f3 :  fm K dim id_vec} 
    {s1 : spc K f1} {s2 : spc K f2} {s3 : spc K f3} (ftr : fm_tr s1 s2) : fm_tr s2 s3 → fm_tr s1 s3 :=
    λftr_, ⟨ftr.1.trans ftr_.1⟩

/-
Convert a (our) basis (fin dim → pt_n K dim) to a Lean matrix
-/
def basis_to_matrix (ftok : fin dim → pt_n K dim) : matrix (fin dim) (fin dim) K :=
    λ i j,
    ((ftok j) i).coord

/-
Convert a frame to a homogeneous matrix. The first column is a 1 + the point coordinates,
The other columns are a 0 + the vectr coordinates
-/
def fm.to_homogeneous_matrix (f_ : fm K dim id_vec) : matrix (fin (dim + 1)) (fin (dim + 1)) K
    := 
    λ i j, 
    if i=0 ∧ j=0 then 1 
    else if i=0 then 0
    else if j = 0 then (f_.origin ⟨i.1-1, sorry⟩).coord
    else (f_.basis ⟨i.1-1,sorry⟩ ⟨j.1-1, sorry⟩).coord

/-
Convert a point into a "lean vector", with 1 at the top followed by the point's coordinates
-/
def point.to_homogeneous_coords (p : point s) : fin (dim+1) → K
    := 
    λi,
    if i=0 then 1
    else (p.coords ⟨i.1-1, sorry⟩).coord


/-
Convert a vector into a "lean vector", with 0 at the top followed by the vector's coordinates
-/
def vectr.to_homogeneous_coords (v : vectr s) : fin (dim+1) → K
    := 
    λi,
    if i=0 then 0
    else (v.coords ⟨i.1-1, sorry⟩).coord

/-
Convert a "lean vector" with homogeneous coordinates back into our representation
of a point in a particular space
-/
def mk_point_from_homogeneous_coords (coords_:fin (dim+1) → K) : point s
    := 
    let findim : fin dim → pt K := λi, mk_pt K (coords_ ⟨i.1+1,sorry⟩) in
    mk_point' s findim

/-
Convert a "lean vector" with homogeneous coordinates back into our representation
of a vectr in a particular space
-/
def mk_vectr_from_homogeneous_coords (coords_:fin (dim+1) → K) : vectr s
    := 
    let findim : fin dim → vec K := λi, mk_vec K (coords_ ⟨i.1+1,sorry⟩) in
    mk_vectr' s findim

/-
Convert an unframed point into a homogeneous lean vector (1 at the top)
-/
def pt_n.to_homogeneous_coords (p : pt_n K dim) : fin (dim+1) → K
    := 
    λi, if i=0 then 0 
    else (p ⟨i.1-1,sorry⟩).coord

/-
Convert an unframed vector into a homogeneous lean vector (0 at the top)
-/
def vec_n.to_homogeneous_coords (v : vec_n K dim) : fin (dim+1) → K
    :=
    λi, if i=0 then 0 
    else (v ⟨i.1-1,sorry⟩).coord
/-
Convert from a lean vector (with 1 at the top) back into an unframed point in our representation 
-/
def mk_pt_n_from_homogeneous_coords (coords_:fin (dim+1) → K) : pt_n K dim
    := 
    λi, mk_pt K (coords_ ⟨i.1+1,sorry⟩)

/-
Convert from a lean vector (with 0 at the top) back into an unframed vector in our representation 
-/
def mk_vec_n_from_homogeneous_coords (coords_:fin (dim+1) → K) : vec_n K dim
    :=
    λi, mk_vec K (coords_ ⟨i.1+1,sorry⟩)

/-
Exploit's cramer's rule to form a computable inverse for a given matrix.
Used in computing transforms
-/
def matrix.cramer_inverse 
    {dim : ℕ} {K : Type u} [inhabited K] [field K] : matrix (fin dim) (fin dim) K →
    matrix (fin dim) (fin dim) K := 
    λm,
    λ i j,
    let detm := m.cramer (λi, m i ⟨0, sorry⟩) ⟨0, sorry⟩ in
    let colj : fin dim → K := λi, if i = j then 1 else 0 in
    (m.cramer colj i)/detm


/-
Helper function for general transforms.
Given a Frame A, this will compute a transform from a vector or point expressed in A,
to the Parent Frame of A, B, and recursively call itself until B is the standard frame. 
Thus, it computes a transform from A to the standard frame. Note that the inverse of this transform is from the standard frame to A.
This is used to crawl through a "Frame Tree" to compute a transform between any two arbitrary frames that
are not necessarily connected.

In the function, note that we match on the frame, and that if it is frame.base, 
it is simply the identity transform since the standard frame is its own parent.
In the deriv case, we turn the coordinates of the frame into a homogeneous matrix
and simply use the homogeneous matrix as the transform.
-/

def to_base_helper' :  fm K dim id_vec → @raw_tr K _ _ dim
| (fm.base dim id_vec) := ⟨
            ⟨   /-base case -/
                (λ p, p),
                (λ p, p),
                begin
                    unfold function.left_inverse,
                    intros,
                    simp *
                end,
                begin
                    unfold function.right_inverse function.left_inverse,
                    intros,
                    simp *
                end
            ⟩,
            ⟨
                (λ v, v),
                begin
                    intros, simp*
                end,
               -- (λ v, ⟨v.coords⟩),
                begin
                    intros, simp *
                end,
                (λ v, v),
                begin
                    unfold function.left_inverse,
                    intros, simp *
                end,
                begin
                    unfold function.left_inverse function.right_inverse,
                    intros, simp *
                end,
            ⟩,
            begin
                simp *,
                --admit   -- TODO: What's this?
            end
        ⟩
| (fm.deriv origin basis ind spans parent) := (⟨
            ⟨/-transform from current->parent-/
                (λ (p : pt_n K dim),
                mk_pt_n_from_homogeneous_coords 
                (((fm.deriv origin basis ind spans parent).to_homogeneous_matrix.mul_vec p.to_homogeneous_coords) : fin (dim + 1) → K)
                : pt_n K dim → pt_n K dim),
                (λ (p : pt_n K dim),
                mk_pt_n_from_homogeneous_coords 
                ((((fm.deriv origin basis ind spans parent).to_homogeneous_matrix.cramer_inverse).mul_vec p.to_homogeneous_coords) : fin (dim + 1) → K)
                : pt_n K dim → pt_n K dim),
                sorry,
                sorry,
            ⟩,
            ⟨
                λv, v,
                sorry,
                sorry,
                sorry,
                sorry,
                sorry
            ⟩,
            sorry /-invert to parent->current and append to current->base-/
⟩ : @raw_tr K _ _ dim).trans (to_base_helper' parent)

/-
Extension method to get a transform from a space to the base (standard) frame 
(essentially a transform from a frame to the standard frame, since spc is mostly 
a wrapper around a frame)
-/
def spc.to_base {f1 :  fm K dim id_vec} (s1 : spc K f1) : @raw_tr K _ _ dim := to_base_helper' f1

/-
Our general function which computes a transform from one space to another.
First computes the transform from the SOURCE space down to the standard space, 
TrA, and then computes the transform of the TARGET space down to the standard
space TrB, and composes TrA with the INVERSE of TrB. This yields a transform
from A to B.
-/
def spc.fm_tr {f1 :  fm K dim id_vec} {f2 :  fm K dim id_vec} (s1 : spc K f1) : Π (s2 : spc K f2),
    fm_tr s1 s2 
    := 
    λ s2,
    ⟨
    let rawtr : @raw_tr K _ _ dim := s1.to_base.trans s2.to_base.symm in
                ⟨
            ⟨
                (λ p : point _, (⟨(rawtr p.1 : pt_n K dim)⟩ : point _)),
                (λ p : point _, (⟨(rawtr p.1 : pt_n K dim)⟩ : point _)),
                sorry,
                sorry
            ⟩,
            ⟨
                (λv : vectr _, (⟨(rawtr.linear v.1 : vec_n K dim)⟩ : vectr _)),
                sorry,
               -- (λ v, ⟨v.coords⟩),
                sorry,
                (λv : vectr _, (⟨(rawtr.linear v.1 : vec_n K dim)⟩ : vectr _)),
                sorry,
                sorry
            ⟩,
            sorry
        ⟩
    ⟩

/-
Extension method for a computed transform which allows you to transform a point 
between two coordinate spaces.
-/

def fm_tr.transform_point  
    {f1 :  fm K dim id_vec} {f2 :  fm K dim id_vec} 
    {s1 : spc K f1} {s2 : spc K f2} (tr:fm_tr s1 s2 ) 
    : point s1 → point s2 :=
    λp,
    tr.to_equiv p

/-
Extension method for a computed transform which allows you to transform a vectr 
between two coordinate spaces. Note there is some magic here because lean "affine 
transforms" only allow you to transform between points.
-/

def fm_tr.transform_vectr  
    {f1 :  fm K dim id_vec} {f2 :  fm K dim id_vec} 
    {s1 : spc K f1} {s2 : spc K f2} (tr:fm_tr s1 s2 ) 
    : vectr s1 → vectr s2 :=
    λv,
    let as_pt : point s1 := ⟨λi, mk_pt K (v.coords i).coord⟩ in
    let tr_pt := (tr.to_equiv as_pt) in
    ⟨λi, mk_vec K (tr_pt.coords i).coord⟩

/-
Requested Dr Sullivan on 6/16.
Simple sugared helper methods to express a point/vector in a different 
coordinate space
-/
def point.expressed_in 
    {dim : ℕ} {id_vec : fin dim → ℕ} {f: fm K dim id_vec} {s : spc K f}  
    {f2: fm K dim id_vec} {s2 : spc K f2} 
    
    (p1 : point s) (s2 : spc K f2) : point s2 :=
    (s.fm_tr s2).transform_point p1

def vectr.expressed_in 
    {dim : ℕ} {id_vec : fin dim → ℕ} {f: fm K dim id_vec} {s : spc K f}  
    {f2: fm K dim id_vec} {s2 : spc K f2} 
    
    (v1 : vectr s) (s2 : spc K f2) : vectr s2 :=
    (s.fm_tr s2).transform_vectr v1

end implicitK