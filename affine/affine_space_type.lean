import linear_algebra.affine_space.basic
import linear_algebra.basis

universes u v w x

variables
    (X : Type u)
    (K : Type v)
    (V : Type w)
    [ring K] 
    [add_comm_group V] 
    [module K V]  
    [affine_space V X]



inductive space  
        (X : Type u)
        (K : Type v)
        (V : Type w)
        [ring K] 
        [add_comm_group V] 
        [module K V]  
        [affine_space V X] : Type (max u v w)
| std                                   : space
| derived (sp : space) (origin : K) (frm : list V)   : space



-- Inductively defined data structure, or TYPE HIERARCHY? The latter I want. Type classes critical.
-- [has_point_type]
-- [has_vector_type]



mutual inductive space, pt, vec, frame 
        (X : Type)
        (K : Type)
        (V : Type)
        [ring K] 
        [add_comm_group V] 
        [module K V]  
        [affine_space V X]
with space : Type
| basic : space
| derived (base_sp : space) (fr : frame) : space
with pt : Type
| base (x : X) : pt
| framed (f : frame) : pt
with vec : Type
| base (x : X) : vec
| framed (f : frame) : vec
with frame : Type
| std : frame
| der (sp : space) (f : frame): frame




mutual inductive space, pt, vec, frame 
        (X : Type u)
        (K : Type u)
        (V : Type u)
        [ring K] 
        [add_comm_group V] 
        [module K V]  
        [affine_space V X]
with space : Type u
| base : space
| derived (fr : frame) : space
with pt : Type u
| base (x : X) : pt
| framed (f : frame) : pt
with vec : Type
| base (x : X) : vec
| framed (f : frame) : vec
with frame : Type u
| std : frame
| der (sp : space) (f : frame): frame
