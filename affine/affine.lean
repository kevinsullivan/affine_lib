import .add_group_action
import .g_space
import algebra.module

universes u v w
variables (X : Type u) (K : Type v) (V : Type w)
[field K] [add_comm_group V] [vector_space K V]


abbreviation affine_space
  (X K V : Type*)
  [field K] [add_comm_group V] [vector_space K V] := add_torsor V X


def affine.diff : X → X → V := sorry

-- TODO: affine combinations, affine transformations, affine frames
