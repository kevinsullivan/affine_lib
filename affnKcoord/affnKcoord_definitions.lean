import .affnK
import linear_algebra.affine_space.affine_equiv
import linear_algebra.matrix
import linear_algebra.basis
import linear_algebra.std_basis

/-
Framed points, vectors, frames
-/

open_locale affine
universes u 

section explicitK

variables 
(K : Type u) [field K] [inhabited K]
(dim : ℕ) 

/-
Frame is built from primitive (fin n)-indexed maps pts and vecs

Constructors are Base (standard) frame or a derived frame 
-/
inductive fm : Πdim : ℕ, Πid_vec:fin dim → ℕ, Type (u)
| base : Πdim : ℕ, Πid_vec:fin dim → ℕ, fm dim id_vec
| deriv 
    {dim : ℕ}
    {id_vec : fin dim → ℕ}
    (origin : pt_n K dim) 
    --(basis : fin dim → vec_n K dim)
    (basis : (fin dim) → (vec_n K dim))
    (basis_independent : linear_independent K basis)
    (basis_spans : submodule.span K (set.range basis))
    (parent : fm dim id_vec)
    : fm dim id_vec

/-
Helper method to retrieve a "parent frame" from a frame.
For a base/standard frame, there is no "parent", so it is it's own parent
For a deriv, simply return the frame it was derived from
-/
@[simp]
def fm.parent 
{K : Type u} [field K] [inhabited K]
{dim : ℕ} {id_vec : fin dim → ℕ}
: fm K dim id_vec → fm K dim id_vec
| (fm.base dim id_vec) := (fm.base dim id_vec)
| (fm.deriv origin basis _ _ parent) := parent

/-
Origin of a frame. For a standard frame, it is the 0 pt, for a derived frame,
the new origin was provided at instantiation.
-/
@[simp]
def fm.origin
{K : Type u} [field K] [inhabited K]
{dim : ℕ} {id_vec : fin dim → ℕ}  :
fm K dim id_vec → pt_n K dim
| (fm.base dim id_vec) := (λi, mk_pt K 0)
| (fm.deriv origin basis _ _ parent) := origin

/-
Basis of a frame. For a standard frame, it is the standard basis, for a derived frame,
the basis was provided at instantiation.
-/
@[simp]
def fm.basis 
{K : Type u} [field K] [inhabited K]
{dim : ℕ} {id_vec : fin dim → ℕ} :
fm K dim id_vec → (fin dim → vec_n K dim)
| (fm.base dim id_vec) := (λ i j, if j = i then mk_vec K 1 else mk_vec K 0)
| (fm.deriv origin basis _ _ parent) := (basis:fin dim → vec_n K dim)


/-
Make a derived frame from an existing frame
Arguments are (unframed) origin, (unframed) basis , and parent frame
-/
def mk_fm  {dim : ℕ} {id_vec : fin dim → ℕ}  (p : pt_n K dim) (v : fin dim → vec_n K dim) (f : fm K dim id_vec)
    : fm K dim id_vec:= fm.deriv p v sorry sorry f

/-
Helper function used to merge two frames when creating a product space from two lower dimensional spaces. 
The result of this function will be a block matrix which contains the two lower dimensional frames along the diagonal.
-/
@[simp]
def merge_prod_fm 
    {K : Type u} [inhabited K] [field K] 
    {dim1 : ℕ} {id_vec1 : fin dim1 → ℕ} --(f1 : fm K dim1 id_vec1)
    {dim2 : ℕ} {id_vec2 : fin dim2 → ℕ} --(f2 : fm K dim2 id_vec2)
    :  fm K dim1 id_vec1 → fm K dim2 id_vec2 → fm K (dim1+dim2) (add_maps id_vec1 id_vec2)
| (fm.deriv o1 b1 _ _ p1) (fm.deriv o2 b2 _ _ p2) := fm.deriv (add_maps o1 o2) 
        (λi, 
            if lt:i.1<dim1 then (add_maps (b1 ⟨i.1,sorry⟩) (mk_vec_n K dim2 ⟨list.repeat dim2 0, sorry⟩))
            else (add_maps (mk_vec_n K dim1 ⟨list.repeat dim1 0, sorry⟩) (b2 ⟨i.1,sorry⟩)))
         sorry sorry (merge_prod_fm p1 p2)
| (fm.deriv o1 b1 _ _ p1) (fm.base dim2 id_vec2) := fm.deriv (add_maps o1 (fm.base dim2 id_vec2).origin) 
        (λi, 
            if lt:i.1 < dim1 then (add_maps (b1 ⟨i.1,sorry⟩) (mk_vec_n K dim2 ⟨list.repeat dim2 0, sorry⟩))
            else (add_maps (mk_vec_n K dim1 ⟨list.repeat dim1 0, sorry⟩) ((fm.base dim2 id_vec2).basis ⟨i.1,sorry⟩)))
         sorry sorry (merge_prod_fm p1 (fm.base dim2 id_vec2))
| (fm.base dim1 id_vec1) (fm.deriv o2 b2 _ _ p2) := fm.deriv (add_maps (fm.base dim1 id_vec1).origin o2) 
        (λi, 
            if i.1 < dim1 then (add_maps (mk_vec_n K dim1 ⟨list.repeat dim1 0, sorry⟩) (b2 ⟨i.1,sorry⟩))
            else (add_maps ((fm.base dim1 id_vec1).basis ⟨i.1,sorry⟩) (mk_vec_n K dim2 ⟨list.repeat dim2 0, sorry⟩)))
         sorry sorry (merge_prod_fm (fm.base dim1 id_vec1) p2)      
| (fm.base dim1 id_vec1) (fm.base dim2 id_vec2) := fm.base (dim1+dim2) (add_maps id_vec1 id_vec2)

/-
Our instantiation of an affine space. Note, it is essentially a wrapper around a frame, and thus
does not have any underlying set. It is later used to parameterize framed points and vectors.
Most spaces will use the single constructor. The prod constructor can be used when trying to 
create the product of two lower dimensional spaces.
-/
inductive spc : Π{dim : ℕ}, Π{id_vec : fin dim → ℕ},Π(f: fm K dim id_vec), Type u
| single {dim : ℕ} {id_vec : fin dim → ℕ} (f: fm K dim id_vec) : spc f
| prod 
    {dim1 : ℕ} {id_vec1 : fin dim1 → ℕ} (f1: fm K dim1 id_vec1) --(s1 : spc dim1 id_vec1 f1)
    {dim2 : ℕ} {id_vec2 : fin dim2 → ℕ} (f2: fm K dim2 id_vec2) --(s2 : spc dim2 id_vec2 f2)
    : spc (merge_prod_fm f1 f2)--(mk_prod_fm f1 f2)

/-
Helper function to retrieve frame from space (space is simply a wrapper around frame, anyway)
-/
def spc.fm {K : Type u} [inhabited K] [field K] {dim : ℕ} {id_vec : fin dim → ℕ} {f: fm K dim id_vec} (sp : spc K f)
    := f
def spc.frame {K : Type u} [inhabited K] [field K] {dim : ℕ} {id_vec : fin dim → ℕ} {f: fm K dim id_vec} (sp : spc K f)
    := f
@[reducible]
def spc.frame_type {K : Type u} [inhabited K] [field K] {dim : ℕ} {id_vec : fin dim → ℕ} {f: fm K dim id_vec} (sp : spc K f)
    := fm K dim id_vec



/-
Alias for the default constructor of spc
-/
@[simp]
def mk_space  {K : Type u} [inhabited K] [field K] 
{dim : ℕ} {id_vec : fin dim → ℕ} 
    (f : fm K dim id_vec) : spc K f  :=
  spc.single f
/-
Alias for the prod constructor of spc
-/
@[simp]
def mk_prod_spc
    {K : Type u} [inhabited K] [field K] 
    {dim1 : ℕ} {id_vec1 : fin dim1 → ℕ} {f1 : fm K dim1 id_vec1} (s1 : spc K f1)
    {dim2 : ℕ} {id_vec2 : fin dim2 → ℕ} {f2 : fm K dim2 id_vec2} (s2 : spc K f2)
    : spc K (merge_prod_fm f1 f2) := spc.prod f1 f2



end explicitK

section implicitK

variables 
{K : Type u} [field K] [inhabited K] 
{dim : nat} {id_vec : fin dim → nat }{f : fm K dim id_vec} (s : spc K f)
{dim2 : nat } {id_vec2 : fin dim2 → nat} {f2 : fm K dim2 id_vec2} (s2 : spc K f2)

/-
A framed (parameterized by the space encapsulating the frame) point.
Contains an unframed point describing its coordinates. 
-/
@[ext]
structure point {f : fm K dim id_vec} (s : spc K f) :=
(coords : pt_n K dim)

/-
Constructor functions to make points
-/
@[simp]
def mk_point' (p : pt_n K dim) : point s := point.mk p  

@[simp]
def mk_point (coords_ : vector K dim) : point s := point.mk (mk_pt_n K dim coords_)  

/-
Combine two points to get their coordinate-wise cartesian product in a space that is
the product of the underlying respective spaces.
-/
@[simp]
def mk_point_prod  
    {dim : ℕ} {id_vec : fin dim → ℕ} {f: fm K dim id_vec} {s : spc K f}  
    {dim2 : ℕ} {id_vec2 : fin dim2 → ℕ} {f2: fm K dim2 id_vec2} {s2 : spc K f2} 
    
    (p1 : point s) (p2 : point s2) : point (mk_prod_spc s s2)
    := ⟨add_maps p1.coords p2.coords⟩

@[simp]
def point.space {dim : ℕ} {id_vec : fin dim → ℕ} {f: fm K dim id_vec} {s : spc K f} 
    (p : point s) : spc K _ := s
/-
A framed (parameterized by the space encapsulating the frame) vector.
Contains an unframed vector describing its coordinates. 
-/
@[ext]
structure vectr {f : fm K dim id_vec} (s : spc K f) :=
(coords : vec_n K dim)

/-
Same as for points, constructor functions and a product constructor.
-/
@[simp]
def mk_vectr' (p : vec_n K dim) : vectr s := vectr.mk p  
@[simp]
def mk_vectr (coords_ : vector K dim) : vectr s := vectr.mk (mk_vec_n K dim coords_)  

@[simp]
def mk_vectr_prod 
    {dim : ℕ} {id_vec : fin dim → ℕ} {f: fm K dim id_vec} {s : spc K f}  
    {dim2 : ℕ} {id_vec2 : fin dim2 → ℕ} {f2: fm K dim2 id_vec2} {s2 : spc K f2} 
    (p1 : vectr s) (p2 : vectr s2) : vectr (mk_prod_spc s s2)
    := ⟨add_maps p1.coords p2.coords⟩

@[simp]
def vectr.space {dim : ℕ} {id_vec : fin dim → ℕ} {f: fm K dim id_vec} {s : spc K f} 
    (v : vectr s) : spc K _ := s

/-
Used to make a frame using framed points and vectors. Simply use their coordinates,
but their underlying frame is noted as the parent of the derived frame
-/
def mk_frame {f : fm K dim id_vec} {s : spc K f}  (p : point s) (v : fin dim → vectr s) :=
fm.deriv p.coords (λi, (v i).coords) sorry sorry f   -- TODO: make sure v ≠ 0 (erasing tyoe info)
                                      -- TODO: snd arg is really a basis for the vs
end implicitK
