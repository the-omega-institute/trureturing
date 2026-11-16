/- GID: D5/S3/Quantum/OriginExclusionSegmentRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/OriginExclusionSegmentRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Recenter the quadratic ball constraint used in the XI origin-control model. -/

/-
proof_shape: b_constraint_recenter: content
escape_witness: hident establishes the translated-ball identity by ring and is used on the live path to the equivalence.
admission_basis: escape-witness
Direct frozen dependencies: none (pinned Mathlib only).
-/

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.OriginExclusionSegmentRigidity

/-- The quadratic constraint on a real `b` coordinate is exactly a translated ball. -/
theorem b_constraint_recenter
    (t b : ℝ) :
    b ^ 2 ≤ t * (1 - t) ↔
      (t - (1 / 2 : ℝ)) ^ 2 + b ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
  have hident : t * (1 - t) = (1 / 2 : ℝ) ^ 2 - (t - (1 / 2 : ℝ)) ^ 2 := by ring
  rw [hident]
  constructor <;> intro h <;> linarith

end D5.S3.Quantum.OriginExclusionSegmentRigidity
