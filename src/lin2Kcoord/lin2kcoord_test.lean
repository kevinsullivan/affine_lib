/-
© 2021 by the Rector and Visitors of the University of Virginia
-/

import .lin2kcoord

/-
This file tests and illustrates the use of lin2kcoord.lean. 
Note: When writing and proving propositions here, be sure 
to explicitly declare the types of scalars and tuples. In
this file, we've let K = ℚ, the rationals. If you make the
mistake of writing 5 instead of (5 : ℚ), for example, you
might run into mysterious failures to simplify expressions.
-/

-- Define a few 2D values in ℚ × ℚ
def v1 := ((1, 1) : ℚ × ℚ)
def v2 := ((-1,1) : ℚ × ℚ)

/- 
Test the addition and scalar multiplication
operators provided by the module typeclass
-/
def v3 := v1 + v2       -- expect (0,2) : ℚ × ℚ
def v4 := (5 : ℚ) • v3  -- expect (0,10) : ℚ × ℚ

-- element addition, abstract now
example : v3 = (0,2) := 
begin
unfold v1 v2 v3,
simp,
trivial,
end

example : v4 = ((0,10) : ℚ × ℚ) :=
begin
unfold v4 v3 v2 v1,
norm_num,
end

