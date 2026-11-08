/- GID: D5/S3/Arith/Robin/ForwardKernel/FourthMomentKurtosis
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/FourthMomentKurtosis
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Brownian fourth moments give explicit dyadic limits and strict excess kurtosis. -/

import D5.S3.Arith.Robin.ForwardKernel.MomentTransfer
import D5.S3.Arith.Robin.ForwardKernel.BrownianFourthKernel
import D5.S3.Arith.Robin.ForwardKernel.FourthMomentInterfaceBridge
import D5.S3.Arith.Robin.ForwardKernel.DyadicMeanSquareAsymptotic

/-! Second and fourth profile moments under the fourth-order Brownian interface. -/

namespace D5.S3.Arith.Robin.ForwardKernel.FourthMomentKurtosis

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs ProfileKernelDefs DyadicProbability MomentTransferDefs
open FourthMomentBandDefs BrownianFourthKernel FourthMomentInterfaceBridge

noncomputable section
set_option autoImplicit false

/-- The variance-band asymptotic gives the normalized second profile moment. -/
theorem dyadicZ_second_moment_tendsto
    {E g : ℝ → ℝ} {α θ β : ℝ}
    (hE : LocallyBoundedMeasurable E)
    (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β)
    (hg : ProfileIntegrable g) :
    Tendsto (fun X : ℝ => ∫ x, dyadicZ E θ g X x ^ 2 ∂dyadicProbabilityMeasure X)
      atTop (𝓝 ((2 ^ kappa θ - 1) * Q g / Real.log 2)) := by
  have hm := (DyadicMeanSquareAsymptotic.profile_kernel_dyadic_mean_square_asymptotic
    hE hB hV hg).div_const (Real.log 2)
  rw [mul_comm (Q g)] at hm
  change Tendsto _ atTop (𝓝 ((2 ^ kappa θ - 1) * Q g / Real.log 2)) at hm
  apply hm.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have hs : 0 ≤ meanSquareScale θ X :=
    (mul_pos (Real.rpow_pos_of_pos (by linarith : 0 < X) _) (Real.log_pos hX)).le
  rw [dyadicProbabilityMeasure_integral (by linarith) _]
  simp_rw [dyadicZ, div_pow, Real.sq_sqrt hs,
    div_right_comm _ (meanSquareScale θ X) _, intervalIntegral.integral_div]
  ring

/-- The fourth Brownian mixed-moment limit yields explicit second and fourth moments;
every nonzero profile has a fourth-moment limit strictly above the Gaussian value. -/
theorem fixed_dyadic_positive_excess_kurtosis
    {E g : ℝ → ℝ} {α θ β C₄ : ℝ}
    (hE : LocallyBoundedMeasurable E)
    (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β)
    (h₄ : FourthMomentBandBoundFor E α β C₄)
    (hg : ProfileIntegrable g)
    (hlim : ∀ s : Fin 4 → ℝ,
      (∀ i, s i ∈ Icc (0 : ℝ) 1) →
      Tendsto (fun X : ℝ => dyadicMixedMoment E θ X 4 s) atTop
        (𝓝 (dyadicMomentConstant θ * kappa θ ^ 2 * brownianW4 s))) :
    Tendsto (fun X : ℝ => ∫ x, dyadicZ E θ g X x ^ 2 ∂dyadicProbabilityMeasure X)
      atTop (𝓝 ((2 ^ kappa θ - 1) * Q g / Real.log 2)) ∧
    Tendsto (fun X : ℝ => ∫ x, dyadicZ E θ g X x ^ 4 ∂dyadicProbabilityMeasure X)
      atTop (𝓝 (3 * kappa θ * (2 ^ (2 * kappa θ) - 1) * Q g ^ 2 /
        (2 * Real.log 2))) ∧
    (¬ (g =ᵐ[unitMeasure] 0) →
      3 * ((2 ^ kappa θ - 1) * Q g / Real.log 2) ^ 2 <
        3 * kappa θ * (2 ^ (2 * kappa θ) - 1) * Q g ^ 2 / (2 * Real.log 2)) := by
  have hθ0 : 0 < θ := hB.1.trans hB.2.1
  have hθ1 : θ < 1 := hB.2.2.1.trans hB.2.2.2
  have hκ : 0 < kappa θ := sub_pos.mpr hθ1
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · exact dyadicZ_second_moment_tendsto hE hB hV hg
  · have hM : MomentInterface E θ 4
        (fun s => dyadicMomentConstant θ * kappa θ ^ 2 * brownianW4 s) := by
      refine ⟨fourth_moment_bound_interface hE hB h₄, ?_, hlim⟩
      unfold brownianW4
      fun_prop
    have hm := MomentTransfer.moment_transfer hE hθ0 hθ1 (by norm_num : 0 < 4) hg hM
    have hi : (∫ s, (∏ i, g (s i)) *
          (dyadicMomentConstant θ * kappa θ ^ 2 * brownianW4 s) ∂cubeMeasure 4) =
        3 * kappa θ * (2 ^ (2 * kappa θ) - 1) * Q g ^ 2 / (2 * Real.log 2) := by
      simp_rw [show ∀ s : Fin 4 → ℝ, (∏ i, g (s i)) *
          (dyadicMomentConstant θ * kappa θ ^ 2 * brownianW4 s) =
          (dyadicMomentConstant θ * kappa θ ^ 2) *
            ((∏ i, g (s i)) * brownianW4 s) from fun s => by ring]
      rw [integral_const_mul, brownianW4_integral hg]
      unfold dyadicMomentConstant
      field_simp [hκ.ne', hl.ne']
    rwa [hi] at hm
  · intro hg_ne
    have hQ : 0 < Q g := (ProfileQuadraticForm.Q_pos_iff hg).mpr hg_ne
    have hp : 0 < (2 : ℝ) ^ kappa θ - 1 :=
      sub_pos.mpr (Real.one_lt_rpow (by norm_num) hκ)
    have hL : 0 < ((2 ^ kappa θ - 1) * Q g / Real.log 2) ^ 2 := by positivity
    apply (lt_div_iff₀ hL).mp
    convert three_lt_kurtosis_ratio hκ using 1
    field_simp [hQ.ne', hp.ne', hl.ne']

end
end D5.S3.Arith.Robin.ForwardKernel.FourthMomentKurtosis
