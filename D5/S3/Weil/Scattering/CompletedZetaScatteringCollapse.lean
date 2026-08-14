/- GID: D5/S3/Weil/Scattering/CompletedZetaScatteringCollapse
   generality: I
   mirror-B: D5/B/S3/Weil/Scattering/CompletedZetaScatteringCollapse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The completed-zeta scattering quotient collapses globally off its zero set. -/

import D5.S3.Weil.Scattering.CompletedZetaScatteringQuotient

namespace D5.S3.Weil.Scattering.CompletedZetaScatteringCollapse

open D5.S3.Zeros.CompletedZeta

/-- The completed-zeta functional equation collapses its scattering quotient to one
whenever the denominator is nonzero. -/
theorem completed_zeta_scattering_quotient_eq_one (s : ℂ)
    (hden : completedZetaReading s ≠ 0) :
    completedZetaReading (1 - s) / completedZetaReading s = 1 := by
  have hreflection : completedZetaReading (1 - s) = completedZetaReading s := by
    change completedRiemannZeta (1 - s) = completedRiemannZeta s
    exact completedRiemannZeta_one_sub s
  rw [hreflection, div_self hden]

example (s : ℂ) (hden : completedZetaReading s ≠ 0) :
    completedZetaReading (1 - s) / completedZetaReading s = 1 :=
  completed_zeta_scattering_quotient_eq_one s hden

end D5.S3.Weil.Scattering.CompletedZetaScatteringCollapse
