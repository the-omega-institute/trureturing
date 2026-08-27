/- GID: D5/S3/Observer/Conditioning/SelectiveRecordConditioning
   generality: G
   mirror-B: D5/B/S3/Observer/Conditioning/SelectiveRecordConditioning
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A nonzero projected record branch has the unique normalized selective state. -/

import D5.S3.Observer.Conditioning

/- Library-search audit trail (2026-08-27):
   * Exact family hits IsRecordMeasurement, recordWeight, and conditionalState were
     inspected, but the latter defines the target formula and cannot honestly prove this atom.
   * Repository body-shape searches for a supplied branch law and for the normalized projected
     state found no public theorem deriving the selective state.
   * Pinned Mathlib's exact inv_mul_cancel₀ and smul_smul are applied directly. -/

namespace D5.S3.Observer.Conditioning.SelectiveRecordConditioning

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- If a recorded branch has nonzero Born weight and its unnormalized matrix is the
corresponding projection compression, its normalized conditional state is forced. -/
theorem selective_record_conditioning
    {n kappa : Type*} [Fintype n]
    (P : kappa -> Matrix n n ℂ) (rho conditioned : Matrix n n ℂ) (k : kappa)
    (hweight : Matrix.trace (rho * P k) ≠ 0)
    (hbranch :
      Matrix.trace (rho * P k) • conditioned = P k * rho * P k) :
    conditioned =
      (Matrix.trace (rho * P k))⁻¹ • (P k * rho * P k) := by
  calc
    conditioned = 1 • conditioned := (one_smul ℂ conditioned).symm
    _ = ((Matrix.trace (rho * P k))⁻¹ *
          Matrix.trace (rho * P k)) • conditioned := by
      rw [inv_mul_cancel₀ hweight]
    _ = (Matrix.trace (rho * P k))⁻¹ •
          (Matrix.trace (rho * P k) • conditioned) := by
      rw [smul_smul]
    _ = (Matrix.trace (rho * P k))⁻¹ • (P k * rho * P k) := by
      rw [hbranch]

#print axioms selective_record_conditioning

end D5.S3.Observer.Conditioning.SelectiveRecordConditioning
