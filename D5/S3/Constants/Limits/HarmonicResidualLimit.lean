/- GID: D5/S3/Constants/Limits/HarmonicResidualLimit
   generality: G
   mirror-B: D5/B/S3/Constants/Limits/HarmonicResidualLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The normalized harmonic residual converges to one minus Euler's constant. -/

/- Library-search audit trail (2026-08-16):
   * D5 searches found uses of the underlying harmonic limit, but no equivalent public theorem.
   * Loogle returned the exact pinned-Mathlib theorem `Real.tendsto_harmonic_sub_log`.
   * LeanSearch's `/api/search` endpoint returned HTTP 404, so it supplied no search result.
-/

import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace D5.S3.Constants.Limits.HarmonicResidualLimit

open Filter Topology

/-- The normalized residual after subtracting the logarithmic growth of harmonic numbers tends to
one minus the Euler-Mascheroni constant. This closes only the residual-limit clause of the source
atom; its protocol-cost interpretations are not claimed here. -/
theorem harmonic_residual_tendsto_one_sub_euler_constant :
    Tendsto (fun n : ℕ => 1 - ((harmonic n : ℝ) - Real.log n)) atTop
      (𝓝 (1 - Real.eulerMascheroniConstant)) := by
  exact tendsto_const_nhds.sub Real.tendsto_harmonic_sub_log

#print axioms harmonic_residual_tendsto_one_sub_euler_constant

end D5.S3.Constants.Limits.HarmonicResidualLimit
