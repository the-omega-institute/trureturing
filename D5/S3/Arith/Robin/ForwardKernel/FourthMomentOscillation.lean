/- GID: D5/S3/Arith/Robin/ForwardKernel/FourthMomentOscillation
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/FourthMomentOscillation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Variance and fourth moment bounds force positive proportions in both tails. -/

import D5.S3.Arith.Robin.ForwardKernel.FourthMomentMovingBounds
import D5.S3.Arith.Robin.ForwardKernel.FirstOrderInterface
import D5.S3.Arith.Robin.ForwardKernel.MomentTransfer
import D5.S3.Arith.Robin.ForwardKernel.FourthMomentProbability
import D5.S3.Arith.Robin.ForwardKernel.DyadicProbability
import D5.S3.Arith.Robin.ForwardKernel.FourthMomentKurtosis

/-! Both strict profile tails occupy a uniform logarithmic proportion. -/

namespace D5.S3.Arith.Robin.ForwardKernel.FourthMomentOscillation

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs ProfileKernelDefs FourthMomentBandDefs
open FourthMomentMovingBounds FourthMomentProbability DyadicProbability

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma profile_power_log_integrable {E g : ℝ → ℝ} {θ X : ℝ}
    (hE : LocallyBoundedMeasurable E) (hg : ProfileIntegrable g) (hX : 3 ≤ X)
    (n : ℕ) :
    IntervalIntegrable (fun x => profileResponse E θ g x ^ n / x) volume X (2 * X) := by
  have hX0 : 0 < X := by linarith
  have hXX : X ≤ 2 * X := by linarith
  let F := fun x => ∫ s, g s * increment E (s * x ^ θ) x * priceRatio x (s * x ^ θ)
    ∂unitMeasure
  obtain ⟨M, hM, hMb⟩ := WeightRemoval.local_increment_bound hE θ hX0 hXX
  have hF (x : ℝ) (hx : x ∈ Icc X (2 * X)) : ‖F x‖ ≤ profileL1 g * M :=
    WeightRemoval.weighted_profile_integral_bound hg θ (hX.trans hx.1) hM (hMb x hx)
  have hc : ContinuousOn (fun x : ℝ => (Real.sqrt x / x ^ θ) ^ n / x)
      (Icc X (2 * X)) := by
    apply ((Real.continuous_sqrt.continuousOn.div
      (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (hX0.trans_le hx.1)))))
        (fun x hx => (Real.rpow_pos_of_pos (hX0.trans_le hx.1) θ).ne')).pow n |>.div
          continuousOn_id (fun x hx => (hX0.trans_le hx.1).ne')
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hXX).mpr
  apply Integrable.of_bound
    (((WeightRemoval.profileResponse_aestronglyMeasurable hE hg θ hX hXX).pow n).div₀
      measurable_id.aestronglyMeasurable) (|B| * (profileL1 g * M) ^ n)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hx' : x ∈ Icc X (2 * X) := ⟨hx.1.le, hx.2⟩
  have hx0 := hX0.trans_le hx'.1
  have he : profileResponse E θ g x = Real.sqrt x / x ^ θ * F x := by
    have hn := WeightRemoval.normalized_eq (E := E) (g := g) (θ := θ) hx0
    calc
      _ = (profileResponse E θ g x / Real.sqrt x) * Real.sqrt x :=
        (div_mul_cancel₀ _ (Real.sqrt_pos.mpr hx0).ne').symm
      _ = _ := by rw [hn]; dsimp [F]; ring
  change ‖profileResponse E θ g x ^ n / x‖ ≤ _
  rw [he, mul_pow, show (Real.sqrt x / x ^ θ) ^ n * F x ^ n / x =
    ((Real.sqrt x / x ^ θ) ^ n / x) * F x ^ n by ring, norm_mul, norm_pow]
  exact mul_le_mul ((hB x hx').trans (le_abs_self B))
    (pow_le_pow_left₀ (norm_nonneg _) (hF x hx') n) (by positivity) (abs_nonneg _)

/-- Both strict tails have uniformly positive proportions on sufficiently large dyadic intervals. -/
theorem profile_response_two_sided_positive_proportion
    {α θ β : ℝ} (hB : ValidBand α θ β) :
    ∃ B : ℝ, 0 < B ∧ ∀ {E : ℝ → ℝ} {C₄ : ℝ} {g : ℝ → ℝ},
      LocallyBoundedMeasurable E →
      CumulativeVarianceBandAsymptoticFor E α β →
      FourthMomentBandBoundFor E α β C₄ →
      ProfileIntegrable g → ¬ (g =ᵐ[unitMeasure] 0) →
      let K := B * C₄ * profileL1 g ^ 4
      let v := ((2 : ℝ) ^ (1 - θ) - 1) * Q g / 2
      let c := fourthMomentThreshold v K
      let δ := fourthMomentDensity v K
      0 < K ∧ ∀ᶠ X : ℝ in atTop,
        (∫ x, (profileResponse E θ g x / Real.sqrt (meanSquareScale θ X)) ^ 4
          ∂dyadicProbabilityMeasure X) ≤ K ∧
        dyadicProbabilityMeasure X
            {x | profileResponse E θ g x > c * Real.sqrt (meanSquareScale θ X)} ≥
          ENNReal.ofReal δ ∧
        dyadicProbabilityMeasure X
            {x | profileResponse E θ g x < -c * Real.sqrt (meanSquareScale θ X)} ≥
          ENNReal.ofReal δ := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨C, hC, hfour⟩ := profile_response_fourth_moment_bound hB
  refine ⟨C / Real.log 2, div_pos hC hl, ?_⟩
  intro E C₄ g hE hV h₄ hg hg_ne
  have hfour := hfour hE h₄ hg
  have hθ1 : θ < 1 := hB.2.2.1.trans hB.2.2.2
  have hQ := (ProfileQuadraticForm.Q_pos_iff hg).mpr hg_ne
  have hp : 0 < (2 : ℝ) ^ (1 - θ) - 1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num) (by linarith))
  let v := ((2 : ℝ) ^ (1 - θ) - 1) * Q g / 2
  have hv : 0 < v := by dsimp [v]; positivity
  let K := (C / Real.log 2) * C₄ * profileL1 g ^ 4
  let Z := fun X x => profileResponse E θ g x / Real.sqrt (meanSquareScale θ X)
  have hs {X : ℝ} (hX : 1 < X) : 0 < meanSquareScale θ X :=
    mul_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.log_pos hX)
  have hmean : Tendsto (fun X => ∫ x, Z X x ∂dyadicProbabilityMeasure X) atTop (𝓝 0) := by
    simpa only [pow_one, mul_zero, integral_zero, MomentTransferDefs.dyadicZ, Z] using
      MomentTransfer.moment_transfer hE (hB.1.trans hB.2.1) hθ1 (by norm_num : 0 < 1) hg
        (FirstOrderInterface.first_moment_interface hE hB hV)
  have hsecond : Tendsto (fun X => ∫ x, Z X x ^ 2 ∂dyadicProbabilityMeasure X)
      atTop (𝓝 (Q g * ((2 : ℝ) ^ (1 - θ) - 1) / Real.log 2)) := by
    simpa only [MomentTransferDefs.dyadicZ, Z, MomentTransferDefs.kappa, mul_comm (Q g)] using
      FourthMomentKurtosis.dyadicZ_second_moment_tendsto hE hB hV hg
  have hgap : v < Q g * ((2 : ℝ) ^ (1 - θ) - 1) / Real.log 2 := by
    apply (lt_div_iff₀ hl).mpr
    have hlog : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    have hv2 : Q g * ((2 : ℝ) ^ (1 - θ) - 1) = 2 * v := by dsimp [v]; ring
    rw [hv2]
    nlinarith
  have hfour_event : ∀ᶠ X : ℝ in atTop,
      (∫ x, Z X x ^ 4 ∂dyadicProbabilityMeasure X) ≤ K := by
    filter_upwards [hfour, eventually_ge_atTop (4 : ℝ)] with X hfour hX
    have hX0 : 0 < X := by linarith
    have hs0 := hs (show 1 < X by linarith)
    rw [dyadicProbabilityMeasure_integral hX0 _]
    have hs4 : Real.sqrt (meanSquareScale θ X) ^ 4 = meanSquareScale θ X ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt hs0.le]
    dsimp [Z]
    simp_rw [div_pow, hs4, div_right_comm _ (meanSquareScale θ X ^ 2) _,
      intervalIntegral.integral_div]
    have hfour' : (∫ x in X..(2 * X), profileResponse E θ g x ^ 4 / x) ≤
        C * C₄ * profileL1 g ^ 4 * meanSquareScale θ X ^ 2 := by
      simpa only [Even.pow_abs (by decide : Even (4 : ℕ))] using hfour
    apply le_trans (div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right hfour' (sq_nonneg _)) hl.le)
    rw [mul_div_cancel_right₀ _ (pow_ne_zero 2 hs0.ne')]
    dsimp [K]
    exact le_of_eq (by ring)
  have hi {X : ℝ} (hX : 4 ≤ X) (n : ℕ) :
      Integrable (fun x => Z X x ^ n) (dyadicProbabilityMeasure X) := by
    apply dyadicProbabilityMeasure_integrable (by linarith)
    have hn := (profile_power_log_integrable hE hg (θ := θ) (by linarith : 3 ≤ X) n).div_const
      (Real.sqrt (meanSquareScale θ X) ^ n)
    apply hn.congr
    intro x hx
    dsimp [Z]
    rw [div_pow]
    ring
  have hm {X : ℝ} (hX : 4 ≤ X) :
      AEStronglyMeasurable (Z X) (dyadicProbabilityMeasure X) :=
    ((WeightRemoval.profileResponse_aestronglyMeasurable hE hg θ (by linarith) (by linarith)).div₀
      aestronglyMeasurable_const).mono_ac (withDensity_absolutelyContinuous _ _)
  have hK : 0 < K := by
    obtain ⟨X, hfourX, htwo, hX⟩ :=
      (hfour_event.and ((hsecond.eventually (eventually_gt_nhds hgap)).and
        (eventually_ge_atTop (4 : ℝ)))).exists
    let : IsProbabilityMeasure (dyadicProbabilityMeasure X) :=
      dyadicProbabilityMeasure_isProbabilityMeasure (by linarith)
    have hZ4 : Integrable (fun x => (Z X x ^ 2) ^ 2) (dyadicProbabilityMeasure X) := by
      simpa only [← pow_mul] using hi hX 4
    have hcs := ProbabilityTheory.variance_nonneg (fun x => Z X x ^ 2)
      (dyadicProbabilityMeasure X)
    rw [ProbabilityTheory.variance_eq_sub (X := fun x => Z X x ^ 2)
      ((memLp_two_iff_integrable_sq ((hm hX).pow 2)).mpr hZ4)] at hcs
    simp only [Pi.pow_apply, ← pow_mul] at hcs
    have htwo0 : 0 < ∫ x, Z X x ^ 2 ∂dyadicProbabilityMeasure X := hv.trans htwo
    nlinarith [sq_pos_of_pos htwo0]
  refine ⟨hK, ?_⟩
  have hlambda : 0 < fourthMomentLambda v K := by
    unfold fourthMomentLambda fourthMomentK1
    positivity
  have heps : 0 < min (Real.sqrt (v / 2)) (fourthMomentLambda v K / 8) :=
    lt_min (Real.sqrt_pos.mpr (by positivity)) (by positivity)
  have hevent : ∀ᶠ X : ℝ in atTop,
      |∫ x, Z X x ∂dyadicProbabilityMeasure X| <
        min (Real.sqrt (v / 2)) (fourthMomentLambda v K / 8) :=
    hmean.abs.eventually (eventually_lt_nhds (by simpa only [abs_zero] using heps))
  filter_upwards [hfour_event, hsecond.eventually (eventually_gt_nhds hgap), hevent,
    eventually_ge_atTop (4 : ℝ)] with X hfourX htwo hε hX
  have hX0 : 0 < X := by linarith
  have hsqrt := Real.sqrt_pos.mpr (hs (show 1 < X by linarith))
  let : IsProbabilityMeasure (dyadicProbabilityMeasure X) :=
    dyadicProbabilityMeasure_isProbabilityMeasure hX0
  refine ⟨hfourX, ?_⟩
  have hfour' : (∫ x, |Z X x| ^ 4 ∂dyadicProbabilityMeasure X) ≤ K := by
    simpa only [Even.pow_abs (by decide : Even (4 : ℕ))] using hfourX
  have ht := two_sided_positive_proportion_of_moments (v := v) (K := K) (hm hX)
    (by simpa only [pow_one] using hi hX 1) (hi hX 2) (hi hX 4) hv htwo.le hfour' hε.le
  have hepos : {x | Z X x > fourthMomentThreshold v K} =
      {x | profileResponse E θ g x >
        fourthMomentThreshold v K * Real.sqrt (meanSquareScale θ X)} := by
    ext x
    exact lt_div_iff₀ hsqrt
  have heneg : {x | Z X x < -fourthMomentThreshold v K} =
      {x | profileResponse E θ g x <
        -fourthMomentThreshold v K * Real.sqrt (meanSquareScale θ X)} := by
    ext x
    exact div_lt_iff₀ hsqrt
  rwa [hepos, heneg] at ht

end
end D5.S3.Arith.Robin.ForwardKernel.FourthMomentOscillation
