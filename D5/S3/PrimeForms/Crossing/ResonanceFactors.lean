/- GID: D5/S3/PrimeForms/Crossing/ResonanceFactors
   generality: G
   mirror-B: D5/B/S3/PrimeForms/Crossing/ResonanceFactors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The two explicit resonance factors vanish identically exactly at alphabet value three. -/

import Mathlib

namespace D5.S3.PrimeForms.Crossing.ResonanceFactors

/-- The two exceptional deficit factors from residual E.67 are identically zero as
polynomials in `p` and `r` exactly when the alphabet parameter `m` equals three. -/
theorem resonance_factors_identically_zero_iff (m : ℤ) :
    (∀ p r : ℤ,
      2 * r * (m - 3) * (2 * p + r) = 0 ∧
        -2 * r * (m - 3) * (p + r) = 0) ↔
      m = 3 := by
  constructor
  · intro h
    have hzero : 2 * (m - 3) = 0 := by
      simpa using (h 0 1).1
    have hdiff : m - 3 = 0 := (mul_eq_zero.mp hzero).resolve_left (by norm_num)
    exact sub_eq_zero.mp hdiff
  · rintro rfl
    simp

end D5.S3.PrimeForms.Crossing.ResonanceFactors
