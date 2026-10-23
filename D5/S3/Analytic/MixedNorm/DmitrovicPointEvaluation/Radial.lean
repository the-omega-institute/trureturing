/- GID: D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Radial
   generality: G
   mirror-B: D5/B/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Radial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic, mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Real]
   utility: none
   digest: Real radial integral and normalized evaluation for the power family. -/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.Radial

/-- The q-th power of the radial mixed norm, with squared family parameter t. -/
noncomputable def radialIntegral (p q α t : ℝ) : ℝ :=
  2 * α * q * ∫ ρ in (0 : ℝ)..1,
    ρ * (1 - ρ ^ 2) ^ (α * q - 1) * (1 + t * ρ ^ 2) ^ (q / p)

/-- The q-th power of the normalized evaluation at a/(1+αp). -/
noncomputable def evaluationExcess (p q α t : ℝ) : ℝ :=
  let c := 1 / (1 + α * p)
  (1 + c * t) ^ (2 * q / p) * (1 - c ^ 2 * t) ^ (α * q + q / p)

end D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.Radial
