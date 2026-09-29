/- GID: D5/S3/VertexAlgebra/DefectTwoSourceBlindness
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/DefectTwoSourceBlindness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two fixed defect directions cannot detect the cubic character carry. -/

/-
proof_shape: two_source_carry_blind: content
escape_witness: The two-dimensional span is closed under arbitrarily many binary
  compositions, while the determinant needs three independent directions.
admission_basis: escape-witness
Direct frozen dependencies: none.
-/

import D5.S3.VertexAlgebra.FiniteDefectCharacterCarry
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.VertexAlgebra.DefectTwoSourceBlindness

open FiniteDefectCharacterCarry

def plane (g h : E) (a b : ZMod 2) : E := fun i => a * g i + b * h i

/-- A third label made from the same two directions has zero determinant pairing with the carry. -/
theorem two_source_carry_blind (mask g h : E) (a b c d e f : ZMod 2) :
    dot (CharacterCarryCompletion.carry (ell mask) (plane g h a b) (plane g h c d))
      (plane g h e f) = 0 := by
  rw [carry_is_wedge]
  simp [dot, wedge, plane]
  ring_nf
  simp only [show (2 : ZMod 2) = 0 by decide,
    show (6 : ZMod 2) = 0 by decide, mul_zero, add_zero]

end D5.S3.VertexAlgebra.DefectTwoSourceBlindness
