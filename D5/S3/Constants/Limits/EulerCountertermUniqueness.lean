/- GID: D5/S3/Constants/Limits/EulerCountertermUniqueness
   generality: G
   mirror-B: D5/B/S3/Constants/Limits/EulerCountertermUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A vanishing harmonic-logarithmic residual uniquely selects Euler's constant. -/

/- Library-search audit trail (2026-08-28):
   * D5 contains the related transformed limit in `HarmonicResidualLimit`, but no counterterm
     uniqueness theorem.
   * Pinned Mathlib's `Real.tendsto_harmonic_sub_log` gives the canonical limit, and
     `tendsto_nhds_unique` is the exact uniqueness principle applied below.
-/

import Mathlib.NumberTheory.Harmonic.EulerMascheroni

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.Limits.EulerCountertermUniqueness

open Filter Topology

/-- Any constant leaving zero after subtraction from the harmonic-logarithmic residual is the
Euler-Mascheroni constant. -/
theorem euler_counterterm_unique (c : ℝ)
    (residual_tendsto_zero :
      Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log n - c) atTop (𝓝 0)) :
    c = Real.eulerMascheroniConstant := by
  have residual_tendsto_c :
      Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log n) atTop (𝓝 c) := by
    convert residual_tendsto_zero.add_const c using 1 <;> simp
  exact tendsto_nhds_unique residual_tendsto_c Real.tendsto_harmonic_sub_log

#print axioms euler_counterterm_unique

end D5.S3.Constants.Limits.EulerCountertermUniqueness
