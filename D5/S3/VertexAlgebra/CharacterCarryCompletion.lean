/- GID: D5/S3/VertexAlgebra/CharacterCarryCompletion
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/CharacterCarryCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A nonlinear section has a uniform finite-tree record expansion. -/

/-
proof_shape: tree_expansion: content
escape_witness: The character correction is derived from the section and cancels in the
  expansion of every binary tree, including trees with different parentheses.
admission_basis: escape-witness
Direct frozen dependencies: none.
-/

import Mathlib.Algebra.Group.Prod
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.VertexAlgebra.CharacterCarryCompletion

variable {E C : Type*} [AddCommGroup E] [AddCommGroup C]

def carry (ell : E → C) (g h : E) : C := ell g + ell h - ell (g + h)

def compose (ell : E → C) (x y : E × C) : E × C :=
  (x.1 + y.1, x.2 + y.2 + carry ell x.1 y.1)

inductive LabelTree (E : Type*) where
  | leaf : E → LabelTree E
  | fork : LabelTree E → LabelTree E → LabelTree E

def evaluate (ell : E → C) : LabelTree E → E × C
  | .leaf g => (g, 0)
  | .fork left right => compose ell (evaluate ell left) (evaluate ell right)

def total : LabelTree E → E
  | .leaf g => g
  | .fork left right => total left + total right

def characterTotal (ell : E → C) : LabelTree E → C
  | .leaf g => ell g
  | .fork left right => characterTotal ell left + characterTotal ell right

/-- Every finite parenthesization records precisely the lost section character. -/
theorem tree_expansion (ell : E → C) (tree : LabelTree E) :
    evaluate ell tree =
      (total tree, characterTotal ell tree - ell (total tree)) := by
  induction tree with
  | leaf g =>
      simp [evaluate, total, characterTotal]
  | fork left right ihLeft ihRight =>
      simp only [evaluate, total, characterTotal, ihLeft, ihRight, compose, carry]
      congr 1
      abel

end D5.S3.VertexAlgebra.CharacterCarryCompletion
