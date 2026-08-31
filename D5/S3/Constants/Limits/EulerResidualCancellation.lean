/- GID: D5/S3/Constants/Limits/EulerResidualCancellation
   generality: G
   mirror-B: D5/B/S3/Constants/Limits/EulerResidualCancellation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Subtracting the Euler-Mascheroni constant cancels the harmonic-logarithmic residual. -/

/- Library-search audit trail (2026-08-31):
   * D5 contains the residual predicate as a premise in `EulerCountertermUniqueness`
     and a related normalized limit in `HarmonicResidualLimit`, but no theorem
     proving the direct zero-residual statement.
   * Pinned Mathlib supplies the exact canonical input theorem
     `Real.tendsto_harmonic_sub_log`; subtracting its limit gives this result. -/

import Mathlib.NumberTheory.Harmonic.EulerMascheroni

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.Limits.EulerResidualCancellation

open Filter Topology

/-- Subtracting the Euler-Mascheroni constant from the harmonic-logarithmic
sequence leaves a residual tending to zero. -/
theorem harmonic_log_euler_residual_tendsto_zero :
    Tendsto
      (fun n : ℕ => (harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant)
      atTop (𝓝 0) := by
  simpa using
    Real.tendsto_harmonic_sub_log.sub_const Real.eulerMascheroniConstant

#print axioms harmonic_log_euler_residual_tendsto_zero

end D5.S3.Constants.Limits.EulerResidualCancellation
