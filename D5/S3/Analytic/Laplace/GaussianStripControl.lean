/- GID: D5/S3/Analytic/Laplace/GaussianStripControl
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/GaussianStripControl
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A wider holomorphic strip and quadratic vertical growth control Gaussian Laplace inversion. -/

import D5.S3.Analytic.Laplace.PairedPoleRegularity

/-! Wider strip regularity for Gaussian inversion of a paired Laplace transform. -/

namespace D5.S3.Analytic.Laplace.PairedPoleRegularity

structure GaussianStripControl (J : ℂ → ℂ) : Prop where
  holomorphic :
    DifferentiableOn ℂ J {s : ℂ | -(1 / 5 : ℝ) < s.re ∧ s.re < 1}
  growth :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ,
      -(1 / 6 : ℝ) ≤ s.re → s.re ≤ 3 / 4 →
      ‖J s‖ ≤ C * (1 + |s.im|) ^ 2

end D5.S3.Analytic.Laplace.PairedPoleRegularity
