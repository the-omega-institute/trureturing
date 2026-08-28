/- GID: D5/S3/Constants/Limits/EulerCountertermExistenceUniqueness
   generality: G
   mirror-B: D5/B/S3/Constants/Limits/EulerCountertermExistenceUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Euler's constant exists as the unique finite harmonic-log counterterm. -/

import D5.S3.Constants.Limits.EulerCountertermUniqueness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.Limits.EulerCountertermExistenceUniqueness

open Filter Topology

/-- The Euler-Mascheroni constant supplies a zero harmonic-log residual, and every real
counterterm supplying such a residual equals it. -/
theorem euler_counterterm_exists_and_unique :
    (∀ c : ℝ,
      Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log n - c) atTop (𝓝 0) →
        c = Real.eulerMascheroniConstant) ∧
    Tendsto
      (fun n : ℕ =>
        (harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant)
      atTop (𝓝 0) := by
  constructor
  · exact
      D5.S3.Constants.Limits.EulerCountertermUniqueness.euler_counterterm_unique
  · simpa only [sub_self] using
      Real.tendsto_harmonic_sub_log.sub_const Real.eulerMascheroniConstant

#print axioms euler_counterterm_exists_and_unique

end D5.S3.Constants.Limits.EulerCountertermExistenceUniqueness
