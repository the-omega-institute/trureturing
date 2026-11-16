/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MSConjectureOscillation
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MSConjectureOscillation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Montgomery–Soundararajan conjecture forces two-sided positive-proportion profile oscillation. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.MSConjectureBand
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.MSConjectureSampling
import D5.S3.Arith.Robin.ForwardKernel.FourthMomentOscillation

/-! Conditional arithmetic oscillation from the second and fourth moments in
Montgomery–Soundararajan (2004), Conjecture 1. The moving profile implication is derived here. -/

open Set Filter MeasureTheory
open scoped Topology

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
open VarianceTransferDefs FourthMomentBandDefs ProfileKernelDefs
open FourthMomentProbability DyadicProbability
noncomputable section
set_option autoImplicit false

/-- Conjecture 1 gives cumulative variance asymptotics and the fourth moment bound
for the complete Chebyshev error on every strict sublinear exponent band. -/
theorem conjecture_implies_variance_and_fourth_bound (α β : ℝ)
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1) (hMS : MSConjectureTwoFour) :
    CumulativeVarianceBandAsymptoticFor chebyshevError α β ∧
      ∃ C₄ : ℝ, FourthMomentBandBoundFor chebyshevError α β C₄ := by
  obtain ⟨A, hA, hfour⟩ := conjecture_discrete_fourth_upper α β hα hαβ hβ hMS
  refine ⟨?_, fourth_band_bound_of_discrete α β A hα hαβ hβ hA hfour⟩
  intro η hη
  filter_upwards [second_sampling_uniform_of_fourth α β A hα hαβ hβ hA hfour
      (η / 2) (half_pos hη),
    conjecture_discrete_second_uniform α β hα hαβ hβ hMS (η / 2) (half_pos hη),
    eventually_ge_atTop (2 : ℝ)] with Y hs hd hY v hvα hvβ
  obtain ⟨hv, _⟩ := FourthTransfer.FourthMomentAsymptotic.band_lengths
    (by linarith : 1 ≤ Y) hα hαβ hβ hvα hvβ
  have hQ : 0 < Y * v * Real.log (Y / v) :=
    mul_pos (mul_pos (by linarith) (by linarith))
      (band_log β Y v hβ (by linarith) hv hvβ).1
  have hdiff : |continuousPrimeMoment 2 Y v - Y * v * Real.log (Y / v)| ≤
      η * (Y * v * Real.log (Y / v)) :=
    (abs_sub_le _ _ _).trans (by linarith only [hs v hvα hvβ, hd v hvα hvβ])
  change |continuousPrimeMoment 2 Y v / (Y * v * Real.log (Y / v)) - 1| ≤ η
  rw [← div_self hQ.ne', ← sub_div, abs_div, abs_of_pos hQ]
  exact (div_le_iff₀ hQ).mpr hdiff

/-- Under Conjecture 1 for moments two and four, both strict tails of every
nonzero real integrable profile have a uniform positive dyadic logarithmic proportion. -/
theorem ms_conjecture_profile_response_two_sided_positive_proportion
    {α θ β : ℝ} (hB : ValidBand α θ β) (hMS : MSConjectureTwoFour) :
    ∃ B C₄ : ℝ, 0 < B ∧ 0 ≤ C₄ ∧ ∀ {g : ℝ → ℝ},
      ProfileIntegrable g → ¬ (g =ᵐ[unitMeasure] 0) →
      let K := B * C₄ * profileL1 g ^ 4
      let v := ((2 : ℝ) ^ (1 - θ) - 1) * Q g / 2
      let c := fourthMomentThreshold v K
      let δ := fourthMomentDensity v K
      0 < K ∧ ∀ᶠ X : ℝ in atTop,
        (∫ x, (profileResponse chebyshevError θ g x /
          Real.sqrt (meanSquareScale θ X)) ^ 4 ∂dyadicProbabilityMeasure X) ≤ K ∧
        dyadicProbabilityMeasure X
            {x | profileResponse chebyshevError θ g x >
              c * Real.sqrt (meanSquareScale θ X)} ≥ ENNReal.ofReal δ ∧
        dyadicProbabilityMeasure X
            {x | profileResponse chebyshevError θ g x <
              -c * Real.sqrt (meanSquareScale θ X)} ≥ ENNReal.ofReal δ := by
  obtain ⟨hV, C₄, h₄⟩ := conjecture_implies_variance_and_fourth_bound α β
    hB.1 (hB.2.1.trans hB.2.2.1) hB.2.2.2 hMS
  obtain ⟨B, hBpos, hosc⟩ :=
    FourthMomentOscillation.profile_response_two_sided_positive_proportion hB
  refine ⟨B, C₄, hBpos, h₄.1, ?_⟩
  intro g hg hgne
  exact hosc DyadicMeanSquareUpper.discrepancy_locallyBoundedMeasurable hV h₄ hg hgne

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
