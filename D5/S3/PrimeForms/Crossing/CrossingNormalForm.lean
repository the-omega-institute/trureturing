/- GID: D5/S3/PrimeForms/Crossing/CrossingNormalForm
   generality: I
   mirror-B: D5/B/S3/PrimeForms/Crossing/CrossingNormalForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The crossing discriminant has a square normal form and a unique minimum. -/

import D5.S3.PrimeForms.PropagationLegs

/- Library-search audit trail (2026-08-17):
   * Repository searches found `PrimeForms.PropagationLegs.slotDiscriminant`, which is reused
     below, but no theorem giving this expansion, lower bound, or equality characterization.
   * Pinned-Mathlib searches for the full quadratic normal form and its unique minimizer found no
     exact theorem. Exact component hits `add_sq`, `sq_nonneg`, and `sq_eq_zero_iff` are reused.
-/

namespace D5.S3.PrimeForms.Crossing.CrossingNormalForm

open D5.S3.PrimeForms.PropagationLegs

/-- The crossing discriminant with offset `A + B` expands to the source polynomial, is bounded
below by `3A²`, and attains that bound exactly when `B = -A`. This closes only the normal-form
clause of the source atom; it does not assert its integer-surface classification. -/
theorem crossing_normal_form_unique_minimum (A B : ℝ) :
    slotDiscriminant ⟨A, A + B⟩ = 4 * A ^ 2 + 2 * A * B + B ^ 2 ∧
      3 * A ^ 2 ≤ slotDiscriminant ⟨A, A + B⟩ ∧
      (slotDiscriminant ⟨A, A + B⟩ = 3 * A ^ 2 ↔ B = -A) := by
  constructor
  · simp only [slotDiscriminant]
    ring
  constructor
  · simp only [slotDiscriminant]
    exact le_add_of_nonneg_right (sq_nonneg (A + B))
  · simp only [slotDiscriminant]
    constructor
    · intro h
      have hsquare : (A + B) ^ 2 = 0 := by linarith
      have hsum : A + B = 0 := sq_eq_zero_iff.mp hsquare
      linarith
    · intro h
      rw [h]
      ring

#print axioms crossing_normal_form_unique_minimum

end D5.S3.PrimeForms.Crossing.CrossingNormalForm
