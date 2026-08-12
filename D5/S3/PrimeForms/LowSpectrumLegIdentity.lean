/- GID: D5/S3/PrimeForms/LowSpectrumLegIdentity
   generality: I
   mirror-B: D5/B/S3/PrimeForms/LowSpectrumLegIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The recorded low-spectrum leg satisfies its integral quadratic-form identity. -/

import Mathlib.Tactic.NormNum

namespace D5.S3.PrimeForms.LowSpectrumLegIdentity

/-- The recorded discriminant, denominator, and integral leg satisfy the exact
quadratic-form identity underlying the displayed low-spectrum value. -/
theorem low_spectrum_leg_identity :
    (4 : ℕ) * 4357 = 3 * 33 ^ 2 + 119 ^ 2 := by
  norm_num1

end D5.S3.PrimeForms.LowSpectrumLegIdentity
