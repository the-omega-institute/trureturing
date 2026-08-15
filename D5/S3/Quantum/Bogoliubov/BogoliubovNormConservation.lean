/- GID: D5/S3/Quantum/Bogoliubov/BogoliubovNormConservation
   generality: G
   mirror-B: D5/B/S3/Quantum/Bogoliubov/BogoliubovNormConservation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Real Bogoliubov coefficients preserve the unit hyperbolic norm. -/

import Mathlib.Analysis.Complex.Trigonometric

namespace D5.S3.Quantum.Bogoliubov.BogoliubovNormConservation

/-- The standard real Bogoliubov coefficients `alpha = cosh r` and `beta = sinh r`
satisfy the canonical norm-conservation identity. -/
theorem bogoliubov_norm_conservation (r : ℝ) :
    |Real.cosh r| ^ 2 - |Real.sinh r| ^ 2 = 1 := by
  simpa only [sq_abs] using Real.cosh_sq_sub_sinh_sq r

#print axioms bogoliubov_norm_conservation

end D5.S3.Quantum.Bogoliubov.BogoliubovNormConservation
