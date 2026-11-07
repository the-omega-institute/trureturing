/- GID: D5/S3/Arith/Robin/ForwardKernel/DyadicMeanSquareAsymptotic
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/DyadicMeanSquareAsymptotic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Moving-length limits yield dyadic kernel mean squares and large points. -/

import D5.S3.Arith.Robin.ForwardKernel.DyadicMeanSquareUpper
import D5.S3.Arith.Robin.ForwardKernel.WeightRemoval
import D5.S3.Arith.Robin.ForwardKernel.MovingLengthMeanSquare

/-! The dyadic asymptotic and point extraction from a moving-length mean-square limit. -/

namespace D5.S3.Arith.Robin.ForwardKernel.DyadicMeanSquareAsymptotic

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs (triangularAverage triangularPrimitive meanSquareScale increment)
open DyadicMeanSquareUpper (ShortIntervalMeanSquareBound CumulativeVarianceBandAsymptotic)
open ActualVonMangoldtBandCompensation (discrepancy)
open OriginalMovingWindowMoment (width)
open Transport (forwardResponse)
open WeightRemoval (unweightedResponse)
open MellinPolynomialGrowth (VonKochBound)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma point_weight_continuousOn {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun x : ℝ => x ^ (1 / 5 : ℝ) * Real.log x / x) (Icc a b) := by
  exact ((continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (ha.trans_le hx.1)))).mul
    (continuousOn_id.log (fun x hx => ne_of_gt (ha.trans_le hx.1)))).div
      continuousOn_id (fun x hx => ne_of_gt (ha.trans_le hx.1))

private lemma point_weight_scaled {X : ℝ} (hX : 1 < X) :
    (∫ x in X..(2 * X), x ^ (1 / 5 : ℝ) * Real.log x / x) / meanSquareScale X =
      (∫ v in (1 : ℝ)..2, v ^ (-4 / 5 : ℝ)) +
        (∫ v in (1 : ℝ)..2, v ^ (-4 / 5 : ℝ) * Real.log v) / Real.log X := by
  have hX0 : 0 < X := by linarith
  have hlog : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  have hp : X ^ (1 / 5 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hX0 _).ne'
  have hv : ContinuousOn (fun v : ℝ => v ^ (-4 / 5 : ℝ)) (Icc (1 : ℝ) 2) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (by change x ≠ 0; linarith [hx.1]))
  have hvl : ContinuousOn (fun v : ℝ => v ^ (-4 / 5 : ℝ) * Real.log v)
      (Icc (1 : ℝ) 2) := hv.mul (continuousOn_id.log (fun x hx => by change x ≠ 0; linarith [hx.1]))
  have hs := intervalIntegral.smul_integral_comp_mul_left
    (fun x : ℝ => x ^ (1 / 5 : ℝ) * Real.log x / x) (a := 1) (b := 2) X
  simp only [smul_eq_mul, mul_one, mul_comm X 2] at hs
  rw [← hs]
  have he : (∫ v in (1 : ℝ)..2, (X * v) ^ (1 / 5 : ℝ) * Real.log (X * v) / (X * v)) =
      X ^ (1 / 5 : ℝ) / X *
        (Real.log X * (∫ v in (1 : ℝ)..2, v ^ (-4 / 5 : ℝ)) +
          ∫ v in (1 : ℝ)..2, v ^ (-4 / 5 : ℝ) * Real.log v) := by
    calc
      _ = ∫ v in (1 : ℝ)..2, X ^ (1 / 5 : ℝ) / X *
          (Real.log X * v ^ (-4 / 5 : ℝ) + v ^ (-4 / 5 : ℝ) * Real.log v) := by
        apply intervalIntegral.integral_congr
        intro v hv
        have hv0 : 0 < v := by rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hv; linarith [hv.1]
        dsimp only
        rw [Real.mul_rpow hX0.le hv0.le, Real.log_mul hX0.ne' hv0.ne']
        have hpow : v ^ (-4 / 5 : ℝ) = v ^ (1 / 5 : ℝ) / v := by
          rw [← Real.rpow_sub_one hv0.ne']; norm_num
        rw [hpow]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_add ((hv.intervalIntegrable_of_Icc (by norm_num)).const_mul _)
            (hvl.intervalIntegrable_of_Icc (by norm_num)),
          intervalIntegral.integral_const_mul]
  rw [he]
  unfold meanSquareScale
  field_simp [hX0.ne', hp, hlog]

theorem dyadic_point_weight_integral_tendsto :
    Filter.Tendsto
      (fun X =>
        (∫ x in X..(2 * X), x ^ (1 / 5 : ℝ) * Real.log x / x) /
          meanSquareScale X)
      Filter.atTop (nhds (5 * ((2 : ℝ) ^ (1 / 5 : ℝ) - 1))) := by
  have hi : (∫ v in (1 : ℝ)..2, v ^ (-4 / 5 : ℝ)) =
      5 * ((2 : ℝ) ^ (1 / 5 : ℝ) - 1) := by
    rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -4 / 5))]
    norm_num
    ring
  have hz : Tendsto (fun X : ℝ =>
      (∫ v in (1 : ℝ)..2, v ^ (-4 / 5 : ℝ) * Real.log v) / Real.log X)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hh := (tendsto_const_nhds (x := 5 * ((2 : ℝ) ^ (1 / 5 : ℝ) - 1))).add hz
  rw [add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  rw [point_weight_scaled hX, hi]

private lemma normalized_square {x y : ℝ} (hx : 0 ≤ x) :
    (y / Real.sqrt x) ^ 2 = y ^ 2 / x := by
  rw [div_pow, Real.sq_sqrt hx]

private lemma unweighted_normalized_square {x : ℝ} (hx : 0 < x) :
    (unweightedResponse x / Real.sqrt x) ^ 2 =
      triangularAverage discrepancy (x ^ (4 / 5 : ℝ)) x ^ 2 := by
  unfold unweightedResponse
  rw [mul_div_cancel_left₀ _ (Real.sqrt_pos.2 hx).ne']
  rfl

private lemma forward_normalized_memLp (hVK : VonKochBound) {X : ℝ} (hX : 3 ≤ X) :
    MemLp (fun x => forwardResponse x / Real.sqrt x) 2
      (volume.restrict (Ioc X (2 * X))) := by
  obtain ⟨C, hC, hE⟩ := MellinConvergence.error_power_bound (by norm_num : (0 : ℝ) ≤ 1)
    (by
      have h := MellinPolynomialGrowth.vonKoch_power_bound hVK (by norm_num : (0 : ℝ) < 1 / 2)
      norm_num at h ⊢
      exact h)
  let A := 2 * C * (2 : ℝ) ^ (1 : ℝ)
  have hm := MellinConvergence.response_measurable.div Real.continuous_sqrt.measurable
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  have hcont : ContinuousOn (fun x : ℝ => (A * x ^ (1 - 3 / 10 : ℝ) / Real.sqrt x) ^ 2)
      (Icc X (2 * X)) := by
    apply ContinuousOn.pow
    apply ContinuousOn.div
    · exact continuousOn_const.mul (continuousOn_id.rpow_const
        (fun x hx => Or.inl (by change x ≠ 0; linarith [hx.1])))
    · exact Real.continuous_sqrt.continuousOn
    · intro x hx
      exact (Real.sqrt_pos.2 (by linarith [hx.1])).ne'
  apply (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self).mono'
    (hm.pow_const 2).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hx0 : 0 < x := by linarith [hx.1]
  have hb := MellinConvergence.forwardResponse_power_bound hC (by norm_num : (0 : ℝ) ≤ 1)
    hE (by linarith [hx.1] : 3 ≤ x)
  have hd : |forwardResponse x / Real.sqrt x| ≤ A * x ^ (1 - 3 / 10 : ℝ) / Real.sqrt x := by
    rw [abs_div, abs_of_pos (Real.sqrt_pos.2 hx0)]
    exact div_le_div_of_nonneg_right hb (Real.sqrt_nonneg _)
  simpa only [Real.norm_eq_abs, abs_pow, sq_abs, Pi.div_apply] using
    pow_le_pow_left₀ (abs_nonneg _) hd 2

theorem forward_kernel_dyadic_mean_square_asymptotic
    (hVK : VonKochBound)
    (hSV : ShortIntervalMeanSquareBound)
    (hGM : CumulativeVarianceBandAsymptotic) :
    Filter.Tendsto
      (fun X =>
        (∫ x in X..(2 * X), forwardResponse x ^ 2 / x) / meanSquareScale X)
      Filter.atTop (nhds (((2 : ℝ) ^ (1 / 5 : ℝ) - 1) / 3)) := by
  have hMove := MovingLengthMeanSquare.moving_length_mean_square_tendsto
    DyadicMeanSquareUpper.discrepancy_locallyBoundedMeasurable hSV hGM
  have hC : 0 < ((2 : ℝ) ^ (1 / 5 : ℝ) - 1) / 3 := by
    have := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) < 1 / 5)
    positivity
  have hgLimit : Tendsto (fun X => (∫ x in X..(2 * X),
      (unweightedResponse x / Real.sqrt x) ^ 2) / meanSquareScale X) atTop
      (𝓝 (((2 : ℝ) ^ (1 / 5 : ℝ) - 1) / 3)) := by
    apply hMove.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    congr 1
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith : X ≤ 2 * X)] at hx
    exact (unweighted_normalized_square (hX.trans_le hx.1)).symm
  have hg : ∀ᶠ X : ℝ in atTop, MemLp (fun x => unweightedResponse x / Real.sqrt x) 2
      (volume.restrict (Ioc X (2 * X))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have hh := MovingLengthRegularity.triangularAverage_variable_memLp
      DyadicMeanSquareUpper.discrepancy_locallyBoundedMeasurable
      (show Measurable (fun x : ℝ => x ^ (4 / 5 : ℝ)) by fun_prop)
      (by linarith : X ≤ 2 * X) (Real.rpow_pos_of_pos hX (4 / 5 : ℝ))
      (L := (2 * X) ^ (4 / 5 : ℝ)) (fun x hx =>
        ⟨Real.rpow_le_rpow hX.le hx.1 (by norm_num),
          Real.rpow_le_rpow (hX.le.trans hx.1) hx.2 (by norm_num)⟩)
    refine MemLp.ae_eq ?_ hh
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    unfold unweightedResponse
    rw [mul_div_cancel_left₀ _ (Real.sqrt_pos.2 (hX.trans hx.1)).ne']
    rfl
  have hdLimit : Tendsto (fun X => (∫ x in X..(2 * X),
      (forwardResponse x / Real.sqrt x - unweightedResponse x / Real.sqrt x) ^ 2) /
        meanSquareScale X) atTop (𝓝 0) := by
    apply (WeightRemoval.forward_kernel_weight_removal_l2 hVK).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    congr 1
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith : X ≤ 2 * X)] at hx
    dsimp only
    rw [← sub_div, normalized_square (hX.le.trans hx.1)]
  have hh := TriangularMeanSquare.interval_square_tendsto_of_l2_negligible hC.le
    (show ∀ᶠ X : ℝ in atTop, X ≤ 2 * X by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
      linarith)
    (show ∀ᶠ X : ℝ in atTop, 0 < meanSquareScale X by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
      exact mul_pos (Real.rpow_pos_of_pos (by linarith : 0 < X) _) (Real.log_pos hX))
    (show ∀ᶠ X : ℝ in atTop, MemLp (fun x => forwardResponse x / Real.sqrt x) 2
        (volume.restrict (Ioc X (2 * X))) by
      filter_upwards [eventually_ge_atTop (3 : ℝ)] with X hX
      exact forward_normalized_memLp hVK hX)
    hg hgLimit hdLimit
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le (by linarith : X ≤ 2 * X)] at hx
  exact normalized_square (hX.le.trans hx.1)

theorem forward_kernel_dyadic_point
    (hVK : VonKochBound)
    (hSV : ShortIntervalMeanSquareBound)
    (hGM : CumulativeVarianceBandAsymptotic)
    {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / Real.sqrt 15) :
    ∀ᶠ X : ℝ in Filter.atTop,
      ∃ x ∈ Set.Icc X (2 * X),
        c * x ^ (1 / 10 : ℝ) * Real.sqrt (Real.log x) ≤ |forwardResponse x| := by
  have hMS := forward_kernel_dyadic_mean_square_asymptotic hVK hSV hGM
  have hcSq : c ^ 2 < (1 / 15 : ℝ) := by
    have hh := (sq_lt_sq₀ hc0.le (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt 15)).mpr hc
    simpa only [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15)] using hh
  have hp : 0 < (2 : ℝ) ^ (1 / 5 : ℝ) - 1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hC : 0 < ((2 : ℝ) ^ (1 / 5 : ℝ) - 1) / 3 := by positivity
  have hgap : 0 < ((2 : ℝ) ^ (1 / 5 : ℝ) - 1) / 3 -
      c ^ 2 * (5 * ((2 : ℝ) ^ (1 / 5 : ℝ) - 1)) := by nlinarith
  have hd := hMS.sub (dyadic_point_weight_integral_tendsto.const_mul (c ^ 2))
  filter_upwards [hd.eventually (eventually_gt_nhds hgap),
    hMS.eventually (eventually_gt_nhds hC), eventually_gt_atTop (1 : ℝ)] with X hgapX hMSX hX
  have hX0 : 0 < X := by linarith
  have hXX : X ≤ 2 * X := by linarith
  have hS : 0 < meanSquareScale X :=
    mul_pos (Real.rpow_pos_of_pos hX0 _) (Real.log_pos hX)
  by_contra hn
  push Not at hn
  have hne : (∫ x in X..(2 * X), forwardResponse x ^ 2 / x) ≠ 0 := by
    intro hz
    rw [hz, zero_div] at hMSX
    exact (lt_irrefl _ hMSX)
  have hi := intervalIntegral.intervalIntegrable_of_integral_ne_zero hne
  have hw : IntervalIntegrable (fun x : ℝ => x ^ (1 / 5 : ℝ) * Real.log x / x)
      volume X (2 * X) :=
    (point_weight_continuousOn hX0).intervalIntegrable_of_Icc hXX
  have hbound (x : ℝ) (hx : x ∈ Icc X (2 * X)) :
      forwardResponse x ^ 2 / x ≤ c ^ 2 * (x ^ (1 / 5 : ℝ) * Real.log x / x) := by
    have hx0 : 0 < x := hX0.trans_le hx.1
    have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith [hx.1])
    have hnonneg : 0 ≤ c * x ^ (1 / 10 : ℝ) * Real.sqrt (Real.log x) := by positivity
    have hs := (sq_le_sq₀ (abs_nonneg _) hnonneg).mpr (hn x hx).le
    rw [sq_abs, mul_pow, mul_pow, Real.sq_sqrt hlog] at hs
    have he : (x ^ (1 / 10 : ℝ)) ^ 2 = x ^ (1 / 5 : ℝ) := by
      rw [← Real.rpow_mul_natCast hx0.le]
      norm_num
    rw [he] at hs
    calc
      _ ≤ (c ^ 2 * x ^ (1 / 5 : ℝ) * Real.log x) / x :=
        div_le_div_of_nonneg_right hs hx0.le
      _ = _ := by ring
  have hb := intervalIntegral.integral_mono_on hXX hi (hw.const_mul (c ^ 2)) hbound
  rw [intervalIntegral.integral_const_mul] at hb
  have hb' := div_le_div_of_nonneg_right hb hS.le
  rw [mul_div_assoc] at hb'
  linarith

end
end D5.S3.Arith.Robin.ForwardKernel.DyadicMeanSquareAsymptotic
