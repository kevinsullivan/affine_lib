import .affine_coordinate_framed_space
import .affine_space_type
import data.real.basic
import linear_algebra.affine_space.basic
import .affine_coordinate_space_lib

noncomputable theory
open aff_fr

/-
-/


/-
For now we'll work with real affine 3-spaces
-/
def dim := 3            -- pick a dimension (other than 0? TODO)
abbreviation K := ℝ     -- alternative field could be, e.g., ℚ



/- 
    RAW SPACE 

The points and vectors of this space are just
"bare" coordinate dim-tuples (of values from K). There
is no definition of any kind of frame at this juncture.
-/

-- Type aliases for vector and point types in THIS space.
abbreviation pt_coords := (aff_pt_coord_tuple K dim)
abbreviation vec_coords := (aff_vec_coord_tuple K dim)

-- Our representation of that actual affine space
def raw_aff_coord_space : 
    affine_space_type pt_coords K vec_coords 
:= ⟨⟩



/- 
    STD FRAMED RAW SPACE 

The salient feature of this space is that the points
and vectors in its frame are *raw* point and vector
coordinate tuples from the space defined just above.
-/

-- A standard frame on raw coordinate tuple space
def std_frame_on_raw_space : 
    affine_frame pt_coords K vec_coords (fin dim) := 
aff_coord_space_std_frame K dim -- TODO: fn not typed to space



/-
Aliases for point and vector types in THIS space. Note this
points in this space are built by adding our frame to points
in the base space (pt_coords, vec_coords).
-/
abbreviation std_framed_raw_vec := 
    aff_coord_vec 
-- Recall    aff_coord_vec is aff_vec_coords + a frame.
-- Similarly aff_coord_pt  is aff_pt_coords  + a frame.
        pt_coords 
        K 
        vec_coords 
        dim 
        (fin dim) 
        std_frame_on_raw_space  -- here's the frame


abbreviation std_framed_raw_pt := 
    aff_coord_pt 
        pt_coords 
        K 
        vec_coords
        dim
        (fin dim)
        std_frame_on_raw_space  -- here's the frame


-- New affine space
def std_framed_raw_coord_space : 
    affine_space_type 
        std_framed_raw_pt 
        K 
        std_framed_raw_vec 
:= ⟨⟩


/-
    STANDARD FRAMED SPACE

The salient characteristic of this space is that both
points and vectors in the space and points and vectors
in its frames themselves have frames. In particular, 
points and vectors in frames on this space live in the 
framed raw space. 
-/

-- aliases for point and vectors types IN THIS SPACE?
-- formerly K_dim_raw_std_fr_vec and K_dim_raw_std_fr_pt
abbreviation std_framed_vec := 
    aff_coord_vec 
        pt_coords 
        K 
        vec_coords 
        dim 
        (fin dim) 
        std_frame_on_raw_space
abbreviation std_framed_pt := 
    aff_coord_pt 
        pt_coords 
        K 
        vec_coords 
        dim 
        (fin dim) 
        std_frame_on_raw_space


/-
Now we create a frame for this space. To do this we 
first instantiate the standard origin and basis vector
values in the underlying framed raw space, then we put
them together into a frame, and finally we create this
new space from that frame.
-/

/-
Our design to date has us represent coordinate tuples
no matter where used as points and vectors in the raw
space. Among other things, this approach ensures that
the constraints on the first values of these tuples
are enforced (0:K for vectors and 1:K for points).
-/
def pt_coords1 : pt_coords   := ⟨[1,0,0,0], by refl ,by refl⟩
def vec_coords1 : vec_coords := ⟨[0,1,0,0], by refl, by refl⟩ 
def vec_coords2 : vec_coords := ⟨[0,0,1,0], by refl, by refl⟩
def vec_coords3 : vec_coords := ⟨[0,0,0,1], by refl, by refl⟩


/- BUG BUG BUG.

BIG TODO: THIS IS WRONG. FRAME ELEMENTS SHOULD COME
FROM PRECEDING SPACE. LACK OF TYPE CHECKING HERE IS 
A PROBLEM. NOTE: CHANGE TYPE OF STD_FRAMED_VEC1 AND
IT DOESN'T BREAK ANY OF THE TYPING, WHICH IS WRONG. 
FIXED TYPES.
-/
-- Lift tuples to point and vectors w.r.t the raw standard frame
def std_framed_pt1 : std_framed_raw_pt    := ⟨pt_coords1⟩
def std_framed_vec2 : std_framed_raw_vec  := ⟨vec_coords1⟩
def std_framed_vec3 : std_framed_raw_vec  := ⟨vec_coords2⟩
def std_framed_vec1 : std_framed_raw_vec  := ⟨vec_coords3⟩

/-
A function to assemble basis vectors into a *basis*
TODO: Fix this. Should be general utility routine
somewhere, not in the test file. Wrong abstraction 
level at this point.
-/
def to_basis (n:ℕ) {vec_type : Type*} (l : vector vec_type n) 
    : (fin n) → vec_type := 
    λ i : fin n, l.nth i

/-
Create a standard frame whose points and vectors themselves 
have frames, namely the raw standard frame.
-/ 
def std_space_std_frame : 
    affine_frame std_framed_pt K std_framed_vec (fin dim) 
:= 
⟨
    std_framed_pt1, 
    to_basis 
        dim 
        ⟨
            [
                std_framed_vec1,
                std_framed_vec2,
                std_framed_vec3
            ],
            sorry
        ⟩,
    sorry
⟩


-- And now the affine space we were after
-- TODO: Can have pt, vec in different spaces
def std_space : 
    affine_space_type 
        std_framed_pt 
        K 
        std_framed_vec 
:= ⟨⟩


/-
    A DERIVED SPACE

Here we create a new space derived from the standard
space by the definition of a new frame, one with the
original basis vectors permuted. Note the order when
we create the basis.
-/

/-
Abbreviations for points and vectors in the complete 
standard frame. The points and vectors in this complete 
frame are themselves framed in the raw frame.
-/
abbreviation derived_space_vec := 
    aff_coord_vec std_framed_pt K std_framed_vec dim (fin dim) std_space_std_frame
abbreviation derived_space_pt := 
    aff_coord_pt std_framed_pt K std_framed_vec dim (fin dim) std_space_std_frame


/-
TODO: Do we want to create a standard frame for A_dim whose points and vectors
are themselves expressed in terms of this standard frame?
-/


/-
Create basis vectors and points in the complete standard 
frame suitable for constructing a derived, non-standard frame.
Note that the basis vectors in this case are in different order 
than 1, 2, dim (now 2, dim, 1).
-/

/- WAIT WAIT WAIT. Here again we're creating derived (this)
space points and vectors to create a basis for the new space,
but these points should live in the base (std) space.

-/

def derived_space_vec1 : derived_space_vec := ⟨vec_coords2⟩
def derived_space_vec2 : derived_space_vec := ⟨vec_coords3⟩
def derived_space_vec3 : derived_space_vec := ⟨vec_coords1⟩
def derived_space_pt1 : derived_space_pt := ⟨pt_coords1⟩


/-
Use the point and vectors just created to create a non-standard frame.
-/
def derived_space_frame : affine_frame derived_space_pt K derived_space_vec (fin dim) := 
⟨
    derived_space_pt1,
    to_basis dim ⟨[derived_space_vec1,derived_space_vec2,derived_space_vec3],sorry⟩,
    sorry
⟩


/-
Abbreviations for points and vectors in this new non-standard frame
-/
abbreviation K_dim_derived_space_frame_vec := 
    aff_coord_vec derived_space_pt K derived_space_vec dim (fin dim) derived_space_frame
abbreviation K_dim_derived_space_frame_pt := 
    aff_coord_pt derived_space_pt K derived_space_vec dim (fin dim) derived_space_frame

/-
Some points and vectors in this non-standard frame. (Note that in all cases we're using
raw affine points and vectors to supply coordinate tuples for all of these constructors.)
-/
def K_dim_derived_space_frame_vec1 : K_dim_derived_space_frame_vec := ⟨vec_coords2⟩
def K_dim_derived_space_frame_vec2 : K_dim_derived_space_frame_vec := ⟨vec_coords3⟩
def K_dim_derived_space_frame_vec3 : K_dim_derived_space_frame_vec := ⟨vec_coords1⟩
def K_dim_derived_space_frame_pt1 : K_dim_derived_space_frame_pt := ⟨pt_coords1⟩

/-
Test out type checking of affine space algebraic operations: expect succeed.
-/
def vecsub := K_dim_derived_space_frame_vec1 - K_dim_derived_space_frame_vec2 -- expected :pass
def vecptadd := pt_plus_vec K_dim_derived_space_frame_pt1 K_dim_derived_space_frame_vec2 --expected : pass
def vecptaddnotation := K_dim_derived_space_frame_pt1 +ᵥ K_dim_derived_space_frame_vec2 --expected : pass
def ptvecadd := K_dim_derived_space_frame_vec2 +ᵥ K_dim_derived_space_frame_pt1 --expected : pass
def vecptsub := K_dim_derived_space_frame_pt1 -ᵥ K_dim_derived_space_frame_vec2  --K_dim_derived_space_frame_pt1 -ᵥ K_dim_derived_space_frame_vec2 --expected : pass
def pt_sub := K_dim_derived_space_frame_pt1 -ᵥ K_dim_derived_space_frame_pt1 -- expected : pass
def scaled : K_dim_derived_space_frame_vec  := (1:K)•K_dim_derived_space_frame_vec2 

/-
Test type checking of affine space operations: expect fail.
-/
def ptvecsub := K_dim_derived_space_frame_vec2 -ᵥ K_dim_derived_space_frame_pt1 -- expected : fail?
def pt_add := K_dim_derived_space_frame_pt1 +ᵥ K_dim_derived_space_frame_pt1 -- expected : fail
def dif_fr := derived_space_vec1 - K_dim_derived_space_frame_vec2 -- expected : fail

/-
SUMMARY:

We have two frames:

- K_dim_std_frame_complete_vec [points and vectors of the frame are framed in raw frame]
- K_dim_non_standard_frame_vec [points and vectors of the frame are framed in K_dim_std_frame_complete_vec]

Observation: We have frames but we don't have explicit corresponding affine spaces. (Or do we?)
-/

/-
Define affine spaces with increasingly structured frames. 
- The unframed space is a raw affine coordinate space with no explicit frame.
- The raw_std space imposes a frame on this space whose points and vectors in the unframed space.
- The quasi-framed space imposes a frame on this space whose points and vectors are in the raw_std space
- The fully framed space imposes a frame whose points and vectors are in the quasi-framed (compl) space. 
-/
def an_unframed_affine_space : affine_space_type pt_coords K vec_coords := ⟨⟩ 
def a_raw_std_framed_affine_space : affine_space_type std_framed_pt K std_framed_vec := ⟨⟩
def a_quasi_framed_affine_space : affine_space_type derived_space_pt K derived_space_vec := ⟨⟩
def a_fully_framed_affine_space : affine_space_type K_dim_derived_space_frame_pt K K_dim_derived_space_frame_vec := ⟨⟩


/-
Now we'll build two more spaces on top of fully_framed
- derived_frame and derived_space
- derived_frame_2 and derived_space_2
-/


/-
Here's derived_frame and derived space
-/
def derived_frame := 
    aff_lib.affine_coord_nspace.mk_derived_frame
    a_fully_framed_affine_space
            ⟨pt_coords1⟩ 
            ⟨[⟨vec_coords3⟩,⟨vec_coords2⟩,⟨vec_coords1⟩],
                    by refl⟩
                
def derived_space :=
    aff_lib.affine_coord_nspace.mk_derived_from_frame
        a_fully_framed_affine_space
        derived_frame


-- Here's derived_frame_2 with points made in derived_space, followed by derived_space_2
def my_pt := aff_lib.affine_coord_nspace.mk_point derived_space [1,1,1]
def my_v1 := aff_lib.affine_coord_nspace.mk_vec derived_space [0.5,0,0]
def my_v2 := aff_lib.affine_coord_nspace.mk_vec derived_space [0,0.5,1]
def my_v3 := aff_lib.affine_coord_nspace.mk_vec derived_space [0,0,0.5]


def derived_frame_2 := 
    aff_lib.affine_coord_nspace.mk_derived_frame
    derived_space
            (aff_lib.affine_coord_nspace.mk_point derived_space [1,1,1]) 
            ⟨
                [
                    (aff_lib.affine_coord_nspace.mk_vec derived_space [0.5,0,0]),
                    (aff_lib.affine_coord_nspace.mk_vec derived_space [0,0.5,1]),
                    (aff_lib.affine_coord_nspace.mk_vec derived_space [0,0,0.5])
                ], 
                by refl
            ⟩


def derived_space_2 :=
   aff_lib.affine_coord_nspace.mk_derived_from_frame
        derived_space
        derived_frame_2

/-
Given a space returns its base frame (or space), i.e., the frame in terms of which
its frame elements are expressed.
-/

/-

def an_unframed_affine_space 
    : affine_space_type pt_coords K vec_coords 
    := ⟨⟩ 
def a_raw_std_framed_affine_space : affine_space_type K_dim_raw_std_fr_pt K K_dim_raw_std_fr_vec := ⟨⟩
def a_quasi_framed_affine_space : affine_space_type K_dim_std_frame_complete_pt K K_dim_std_frame_complete_vec := ⟨⟩
def a_fully_framed_affine_space : affine_space_type K_dim_non_standard_frame_pt K K_dim_non_standard_frame_vec := ⟨⟩



- get_base_space derived_space_2
                    (affine_space aff_coord_pt K aff_coord_vec der_fr) 
                    :          
        -- expect derived_space
- get_base_space derived_space          
        -- expect a_fully_framed_affine_space
- get_base_space a_fully_framed_affine_space 
                    (affine_space aff_coord_pt K aff_coord_vec quasi_fr)           
        -- expect a_quasi_framed_affine_space
- get_base_space a_quasi_framed_affine_space 
                     (affine_space aff_coord_pt K aff_coord_vec raw_fr)           
        -- expect a_raw_std_framed_affine_space
- get_base_space a_raw_std_framed_affine_space 
                     (affine_space aff_coord_pt K aff_coord_vec unfr_fr)    
        -- expect an_unframed_affine_space
- get_base_space an_unframed_affine_space 
                    : (affine_space tuple_pt K tuple_vec )
        -- expect ???
-/

#check derived_space_2
#check (aff_lib.affine_coord_nspace dim derived_frame_2)

/-
aff coord space:
    
    affine_space_type 
        (aff_coord_pt X K V n ι fr)
        K
        (aff_coord_vec X K V n ι fr)

def affine_coord_space.get_base_space
    {X : Type u} {K : Type v} {V : Type w} {ι : Type*}
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    {n : ℕ}
    {fr : affine_frame X K V ι }
    (sp : affine_coord_space n fr)
    :=
        affine_space_type X K V

-/



def derived_space_2_base := aff_lib.affine_coord_space.get_base_space derived_space_2

-- example : derived_space_2_base = derived_space := rfl       -- nope

def derived_space_base := aff_lib.affine_coord_space.get_base_space derived_space

def a_fully_framed_affine_space_base := aff_lib.affine_coord_space.get_base_space a_fully_framed_affine_space

def another_base := aff_lib.affine_coord_space.get_base_space a_fully_framed_affine_space

def a_quasi_framed_affine_space_base := aff_lib.affine_coord_space.get_base_space a_fully_framed_affine_space

def a_raw_framed_affine_space_base := aff_lib.affine_coord_space.get_base_space a_fully_framed_affine_space


#check derived_space_2_base
/-
    affine_space_type 
        (aff_coord_pt X K V n (fin n) fr)
        K
        (aff_coord_vec X K V n (fin n) fr)
-/


/-
inductive affine_coordinate_space_type
| mk_raw (as : affine_space aff_pt K aff_vec) (o : origin) 
| mk_der (acs : affine_coordinate_space_type) (acf: affine_coordinate_frame)
-/


