/- GID: D5/S3/Arith/Robin/ForwardKernel/FourthMomentBandDefs
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/FourthMomentBandDefs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform fourth moments of fixed increments on an exponent band. -/

import D5.S3.Arith.Robin.ForwardKernel.VarianceTransferDefs

/-! The uniform fourth-moment hypothesis for an abstract real error function. -/

namespace D5.S3.Arith.Robin.ForwardKernel.FourthMomentBandDefs

open MeasureTheory Filter VarianceTransferDefs

noncomputable section

/-- The fourth moment of every increment in the exponent band has the natural upper bound. -/
def FourthMomentBandBoundFor (E : ℝ → ℝ) (α β C₄ : ℝ) : Prop :=
  0 ≤ C₄ ∧
    ∀ᶠ Y : ℝ in atTop, ∀ u : ℝ, Y ^ α ≤ u → u ≤ Y ^ β →
      (∫ x in (1 : ℝ)..Y, |increment E u x| ^ 4) ≤
        C₄ * Y * u ^ 2 * (Real.log (Y / u)) ^ 2

end
end D5.S3.Arith.Robin.ForwardKernel.FourthMomentBandDefs
