/- GID: D5/S3/Arith/Robin/ForwardKernel/FourthMomentInterfaceBridge
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/FourthMomentInterfaceBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourth-moment band bounds control normalized dyadic increments. -/

import D5.S3.Arith.Robin.ForwardKernel.MomentInterfaceBounds
import D5.S3.Arith.Robin.ForwardKernel.FourthMomentMovingBounds

/-! The fourth absolute moment bound in the dyadic moment interface. -/

namespace D5.S3.Arith.Robin.ForwardKernel.FourthMomentInterfaceBridge

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs VarianceTransfer FourthMomentBandDefs
open MomentTransferDefs DyadicProbability

noncomputable section
set_option autoImplicit false

/-- A fourth-moment bound on an exponent band bounds the fourth absolute moments
of all normalized moving increments, uniformly in their unit profile parameter. -/
theorem fourth_moment_bound_interface
    {E : ℝ → ℝ} {α θ β C₄ : ℝ}
    (hE : LocallyBoundedMeasurable E)
    (hB : ValidBand α θ β)
    (h₄ : FourthMomentBandBoundFor E α β C₄) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ X : ℝ in atTop,
        ∀ s ∈ Icc (0 : ℝ) 1,
          (∫ x, |dyadicB E θ s x| ^ 4
            ∂dyadicProbabilityMeasure X) ≤ C := by
  obtain ⟨K, hK, hinc⟩ :=
    FourthMomentMovingBounds.moving_increment_fourth_moment_bound hB
  refine ⟨(K * C₄) / Real.log 2,
    div_nonneg (mul_nonneg hK.le h₄.1) (Real.log_pos (by norm_num)).le, ?_⟩
  apply MomentInterfaceBounds.normalized_even_moment_bound (m := 2) hE
    (hB.1.trans hB.2.1).le (mul_nonneg hK.le h₄.1)
  filter_upwards [hinc hE h₄] with X hinc
  intro s hs
  simpa only [show (2 * 2 : ℕ) = 4 by norm_num, mul_pow, mul_assoc] using hinc s hs

end
end D5.S3.Arith.Robin.ForwardKernel.FourthMomentInterfaceBridge
