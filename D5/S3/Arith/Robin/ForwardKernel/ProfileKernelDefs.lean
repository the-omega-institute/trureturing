/- GID: D5/S3/Arith/Robin/ForwardKernel/ProfileKernelDefs
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/ProfileKernelDefs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The price ratio and moving profile response use the Robin price derivative weight. -/

import D5.S3.Arith.Robin.ForwardKernel.VarianceTransferDefs
import D5.S3.Arith.Robin.ForwardKernel.Transport
import D5.S3.Arith.Robin.MellinWeightedVariation

/-! Price weights for moving profile responses. -/

namespace D5.S3.Arith.Robin.ForwardKernel.ProfileKernelDefs

open VarianceTransferDefs

noncomputable section

/-- The ratio of the Robin price derivative weights at `x + u` and `x`. -/
def priceRatio (x u : ℝ) : ℝ :=
  MellinWeightedVariation.weight (x + u) / MellinWeightedVariation.weight x

/-- The price-weighted response to a profile at the moving length `x^θ`. -/
def profileResponse (E : ℝ → ℝ) (θ : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.sqrt x / (x ^ θ) ^ 2 *
    ∫ u in (0 : ℝ)..(x ^ θ),
      g (u / x ^ θ) * increment E u x * priceRatio x u

/-- The complete Chebyshev response is the constant-profile response at exponent `4/5`. -/
theorem forwardResponse_eq_profileResponse :
    Transport.forwardResponse =
      profileResponse ActualVonMangoldtBandCompensation.discrepancy
        (4 / 5 : ℝ) (fun _ => 1) := by
  funext x
  simp only [Transport.forwardResponse, profileResponse, OriginalMovingWindowMoment.width,
    increment, priceRatio, one_mul]

end

end D5.S3.Arith.Robin.ForwardKernel.ProfileKernelDefs
