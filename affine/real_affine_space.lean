import .aff_coord_space
import data.real.basic


abbreviation real_vec := aff_vec ℝ
abbreviation real_pt  := aff_pt  ℝ

#check real_vec 3
#check real_pt 3

abbreviation r3_vec := real_vec 3
abbreviation r3_pt  := real_pt  3


/-
def ra3space : _ := _

pt, field, vec

pt = aff_pt K n
vec = aff_vec K n
instance : affine_space pt field vec := _

phys_vec := (meters, vec)
phys_pt := (meters, pt)

(meters, vec) + (meters, pt) = (meters, pt_2)
(meters, vec) + (meters, vec) = (meters, vec)
-/



/-
Bottom: look at math, then look at phys, how it fits into DSL
Top down: 
    - geom3d := geometric_euclidean_space("world", 3)
    - geom3d.stdFrame()
    - geom3d.vectorSpace()
    - geom3d.points()
    - someVec3 := vector(geom3d.vectorSpace, [-1,4,2], geom3d.stdFrame)
    - geometric_euclidean_space("world", 3)
    * eval(Lit_Geom_Expr "world" 3) -- i want a physical space
-/ 