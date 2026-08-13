/- GID: D5/S3/Weil/Scattering/ScatteringQuotient
   generality: G
   mirror-B: D5/B/S3/Weil/Scattering/ScatteringQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The real spectral scattering quotient of a completed zeta reading has unit norm. -/

import D5.S3.Zeros.CompletedZeta

namespace D5.S3.Weil.Scattering.ScatteringQuotient

open D5.S3.Zeros.CompletedZeta
open scoped ComplexConjugate

/-- A real spectral parameter gives a unit-modulus quotient of the completed zeta reading at the reflected pair. -/
theorem real_spectral_scattering_quotient_norm (t : ℝ)
    (hden : completedZetaReading (1 / 2 + (t : ℂ) * Complex.I) ≠ 0) :
    ‖completedZetaReading (1 / 2 - (t : ℂ) * Complex.I) /
      completedZetaReading (1 / 2 + (t : ℂ) * Complex.I)‖ = 1 := by
  have hreflection :
      completedZetaReading (1 / 2 - (t : ℂ) * Complex.I) =
        completedZetaReading (1 / 2 + (t : ℂ) * Complex.I) := by
    change completedRiemannZeta (1 / 2 - (t : ℂ) * Complex.I) =
      completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I)
    have harg :
        (1 : ℂ) - (1 / 2 + (t : ℂ) * Complex.I) =
          1 / 2 - (t : ℂ) * Complex.I := by
      push_cast
      ring
    rw [← harg, completedRiemannZeta_one_sub]
  rw [hreflection]
  rw [norm_div, div_self (norm_ne_zero_iff.mpr hden)]

end D5.S3.Weil.Scattering.ScatteringQuotient
