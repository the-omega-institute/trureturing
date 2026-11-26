/- GID: D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianProjectiveCorrection
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianProjectiveCorrection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The canonical Gaussian period correction is recovered from the actual native period-ratio derivative quotient. -/

import D5.S3.Analytic.OriginalHalfBinomialProjective
import D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes

noncomputable section
set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianProjectiveCorrection

open D5.S3.Analytic.OriginalHalfBinomialWronskian (tau)
open D5.S3.Analytic.AbelRatioSchwarzian (preSchwarzian)
open OriginalGaussianFiniteCandidateModes (ell k)

/-- Both directions of the bridge use the actual derivative quotient and the
canonical FiniteMode correction, with no analytic premises beyond the lens. -/
theorem original_correction_projective {r : ℂ} (hr : ‖r‖ < 1) (hc : ‖1 - r‖ < 1) :
    preSchwarzian tau r = -(1 - 2 * r + 2 * k r) / (r * (1 - r)) ∧
      k r = (2 * r - 1) / 2 - r * (1 - r) * preSchwarzian tau r / 2 := by
  have hg := (D5.S3.Analytic.OriginalHalfBinomialProjective.original_tau_projective
    hr hc).2.2.2.1
  have hr0 : r ≠ 0 := by
    intro he
    simpa [he] using hc
  have hc0 : 1 - r ≠ 0 := by
    intro he
    have h1 : r = 1 := by linear_combination -he
    simpa [h1] using hr
  rw [hg]
  dsimp [k, ell]
  constructor <;> field_simp [hr0, hc0] <;> ring

end D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianProjectiveCorrection
