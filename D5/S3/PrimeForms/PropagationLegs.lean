/- GID: D5/S3/PrimeForms/PropagationLegs
   generality: G
   mirror-B: D5/B/S3/PrimeForms/PropagationLegs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: In a crossing slot with discriminant 3A²+u², the three represented values A, (u−A)/2, (u+A)/2 are all √3-legs, and the discriminant square-root reduces to the Pythagorean spectral line √(3+(u/A)²). -/

import Mathlib

namespace D5.S3.PrimeForms.PropagationLegs

/-- A crossing slot carries a base `A` and an offset `u`. -/
structure CrossingSlot where
  A : ℝ
  u : ℝ

/-- The slot discriminant `D = 3A² + u²`. -/
def slotDiscriminant (slot : CrossingSlot) : ℝ := 3 * slot.A ^ 2 + slot.u ^ 2

/-- `leg` is a √3-leg of the slot with companion `other` when `D − 3·leg² = other²`. -/
def IsSqrtThreeLeg (slot : CrossingSlot) (leg other : ℝ) : Prop :=
  slotDiscriminant slot - 3 * leg ^ 2 = other ^ 2

/-- The three represented values `A, (u−A)/2, (u+A)/2` are all √3-legs. -/
theorem three_propagated_legs (slot : CrossingSlot) :
    IsSqrtThreeLeg slot slot.A slot.u ∧
      IsSqrtThreeLeg slot ((slot.u - slot.A) / 2) ((3 * slot.A + slot.u) / 2) ∧
      IsSqrtThreeLeg slot ((slot.u + slot.A) / 2) ((3 * slot.A - slot.u) / 2) := by
  refine ⟨?_, ?_, ?_⟩ <;> · simp only [IsSqrtThreeLeg, slotDiscriminant]; ring

/-- The Pythagorean spectral line: `√(3A²+u²)/|A| = √(3 + (u/A)²)`. -/
theorem spectral_line (A u : ℝ) (hA : A ≠ 0) :
    Real.sqrt (3 * A ^ 2 + u ^ 2) / |A| = Real.sqrt (3 + (u / A) ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_div (by positivity)]
  congr 1
  field_simp

/-- Propagation identity: the three √3-legs together with the spectral-line reduction. -/
theorem propagation_identity (slot : CrossingSlot) (hA : slot.A ≠ 0) :
    (IsSqrtThreeLeg slot slot.A slot.u ∧
      IsSqrtThreeLeg slot ((slot.u - slot.A) / 2) ((3 * slot.A + slot.u) / 2) ∧
      IsSqrtThreeLeg slot ((slot.u + slot.A) / 2) ((3 * slot.A - slot.u) / 2)) ∧
      Real.sqrt (slotDiscriminant slot) / |slot.A| =
        Real.sqrt (3 + (slot.u / slot.A) ^ 2) := by
  exact ⟨three_propagated_legs slot, spectral_line slot.A slot.u hA⟩

end D5.S3.PrimeForms.PropagationLegs
