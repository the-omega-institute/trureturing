/- GID: D5/S3/Zeros/MirrorPairEnvelope
   generality: G
   mirror-B: D5/B/S3/Zeros/MirrorPairEnvelope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A mirror-pair exponential envelope is twice the hyperbolic cosine. -/

import Mathlib.Analysis.Complex.Trigonometric

namespace D5.S3.Zeros.MirrorPairEnvelope

/-- The two exponential branches of a mirror pair combine as twice the hyperbolic cosine. -/
theorem mirror_pair_envelope_eq_two_cosh (beta u : ℝ) :
    Real.exp ((beta - 1 / 2) * u) + Real.exp (-((beta - 1 / 2) * u)) =
      2 * Real.cosh ((beta - 1 / 2) * u) := by
  rw [Real.cosh_eq]
  ring

/-- The real parameter domain is inhabited. -/
example : ℝ × ℝ := (0, 0)

/-- With no hypotheses to discharge, the universal statement specializes at an explicit input. -/
example :
    Real.exp ((0 - 1 / 2) * 0) + Real.exp (-((0 - 1 / 2) * 0)) =
      2 * Real.cosh ((0 - 1 / 2) * 0) :=
  mirror_pair_envelope_eq_two_cosh 0 0

end D5.S3.Zeros.MirrorPairEnvelope
