import .affine_space_type
import data.real.basic

open space

def bsp : space ℝ ℝ ℝ := space.std 
def dsp1 : space ℝ ℝ ℝ := space.derived 0 [0,0]
def dsp2 : space ℝ ℝ ℝ := space.derived 0 [0]






/-
A few things to note:

(1) We can specialize our generic affine_space_type definition
(2) We can't instantiate disjoint affine space of the same type 
(3) Can we express news points and vectors in terms of this frame?
-/