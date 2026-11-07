/- GID: D5/S3/Arith/Robin/ForwardKernel/WeightRemoval
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/WeightRemoval
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Von Koch control removes the correlated price weight from the forward kernel at logarithmic-square scale. -/

import D5.S3.Arith.Robin.ForwardKernel.WeightControl
import D5.S3.Arith.Robin.ForwardKernel.DyadicMeanSquareUpper
import D5.S3.Arith.Robin.ForwardKernel.Transport
import D5.S3.Arith.Robin.ForwardKernel.MellinPolynomialGrowth

namespace D5.S3.Arith.Robin.ForwardKernel.WeightRemoval

open Set MeasureTheory Filter
open scoped Topology

noncomputable section
set_option autoImplicit false

open ActualVonMangoldtBandCompensation (discrepancy)
open OriginalMovingWindowMoment (width)
open ForwardKernel.Transport (forwardResponse)
open ForwardKernel.MellinPolynomialGrowth (VonKochBound)
open ForwardKernel.WeightControl (weightRatio weightRatio_sub_one)
open VarianceTransferDefs (triangularAverage triangularPrimitive meanSquareScale)

def unweightedResponse (x : ℝ) : ℝ :=
  Real.sqrt x * triangularAverage discrepancy (width x) x

theorem discrepancy_increment_vonKoch_bound (hVK : VonKochBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in Filter.atTop,
      ∀ u ∈ Set.Icc (0 : ℝ) (width x),
        |discrepancy (x + u) - discrepancy x| ≤ C * Real.sqrt x * (Real.log x) ^ 2 := by
  obtain ⟨C₀, t₀, hC₀, ht₀, hbound⟩ := hVK
  refine ⟨16 * C₀ + 1, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max 4 t₀)] with x hx u hu
  have hx4 : 4 ≤ x := le_max_left _ _ |>.trans hx
  have hxt : t₀ ≤ x := le_max_right _ _ |>.trans hx
  have hx0 : 0 < x := by linarith
  have hwle : width x ≤ x := by
    unfold width
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le (x := x) (y := (4 / 5 : ℝ))
        (z := (1 : ℝ)) (by linarith) (by norm_num))
  have hxu : x + u ≤ 2 * x := by linarith [hu.2, hwle]
  have hxu0 : 0 ≤ x + u := by linarith [hu.1]
  have hybound : |discrepancy (x + u)| ≤ C₀ * Real.sqrt (x + u) * (Real.log (x + u)) ^ 2 :=
    hbound (x + u) (by linarith [hu.1])
  have hxbound : |discrepancy x| ≤ C₀ * Real.sqrt x * (Real.log x) ^ 2 :=
    hbound x hxt
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlogxu : 0 ≤ Real.log (x + u) := Real.log_nonneg (by linarith [hu.1])
  have hlog_le : Real.log (x + u) ≤ 2 * Real.log x := by
    have hlog2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
    have hlogadd : Real.log (x + u) ≤ Real.log (2 * x) :=
      Real.log_le_log (by linarith [hu.1]) hxu
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)] at hlogadd
    linarith
  have hsqrt_le : Real.sqrt (x + u) ≤ 2 * Real.sqrt x := by
    have hs := Real.sqrt_le_sqrt hxu
    have hs2 : Real.sqrt (2 * x) ≤ 2 * Real.sqrt x := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have htwo : Real.sqrt (2 : ℝ) ≤ 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_right htwo (Real.sqrt_nonneg x)
    exact hs.trans hs2
  have hprod : Real.sqrt (x + u) * (Real.log (x + u)) ^ 2 ≤
      (2 * Real.sqrt x) * (2 * Real.log x) ^ 2 := by
    gcongr
  have hCprod : C₀ * Real.sqrt (x + u) ≤ C₀ * (2 * Real.sqrt x) :=
    mul_le_mul_of_nonneg_left hsqrt_le hC₀
  have hCprod' : C₀ * Real.sqrt (x + u) * (Real.log (x + u)) ^ 2 ≤
      C₀ * (2 * Real.sqrt x) * (2 * Real.log x) ^ 2 := by
    have hlogsq : (Real.log (x + u)) ^ 2 ≤ (2 * Real.log x) ^ 2 := by
      nlinarith [hlog_le, hlogxu, hlogx]
    exact mul_le_mul hCprod hlogsq (by positivity) (by positivity)
  have hybound' : |discrepancy (x + u)| ≤ 8 * C₀ * Real.sqrt x * (Real.log x) ^ 2 := by
    calc
      _ ≤ C₀ * (2 * Real.sqrt x) * (2 * Real.log x) ^ 2 :=
        hybound.trans hCprod'
      _ = 8 * C₀ * Real.sqrt x * (Real.log x) ^ 2 := by ring
  have hdiff := (abs_sub _ _).trans (add_le_add hybound' hxbound)
  have hnonneg : 0 ≤ Real.sqrt x * (Real.log x) ^ 2 :=
    mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)
  nlinarith

theorem forward_kernel_weight_removal (hVK : VonKochBound) :
    Asymptotics.IsBigO Filter.atTop
      (fun x => forwardResponse x - unweightedResponse x)
      (fun x => (Real.log x) ^ 2) := by
  rw [Asymptotics.isBigO_iff]
  obtain ⟨C, hC, hinc⟩ := discrepancy_increment_vonKoch_bound hVK
  refine ⟨4 * C, ?_⟩
  filter_upwards [hinc, eventually_ge_atTop (4 : ℝ)] with x hxu hx4
  simp only [Real.norm_eq_abs, abs_pow, sq_abs]
  have hx0 : 0 < x := by linarith
  have hw0 : 0 < width x := by
    unfold width
    exact Real.rpow_pos_of_pos hx0 _
  have hx1 : 1 < x := by linarith
  have hI0 : IntervalIntegrable
      (fun u : ℝ => discrepancy (x + u) - discrepancy x) volume 0 (width x) := by
    exact (VarianceTransfer.increment_comp_integrableOn
      DyadicMeanSquareUpper.discrepancy_locallyBoundedMeasurable
      isCompact_uIcc continuous_id continuous_const).intervalIntegrable
  have hIw : IntervalIntegrable
      (fun u : ℝ => (discrepancy (x + u) - discrepancy x) *
        (MellinWeightedVariation.weight (x + u) /
          MellinWeightedVariation.weight x)) volume 0 (width x) :=
    Transport.forwardResponse_intervalIntegrable hx1
  have hdiff_eq : forwardResponse x - unweightedResponse x =
      Real.sqrt x / width x ^ 2 *
        ∫ u in (0 : ℝ)..width x,
          (discrepancy (x + u) - discrepancy x) *
            (weightRatio x (u / width x) - 1) := by
    have hsub := intervalIntegral.integral_sub hIw hI0
    have hsub' : (∫ u in (0 : ℝ)..width x,
          (discrepancy (x + u) - discrepancy x) *
            (weightRatio x (u / width x) - 1)) =
        (∫ u in (0 : ℝ)..width x,
          (discrepancy (x + u) - discrepancy x) *
            (MellinWeightedVariation.weight (x + u) /
              MellinWeightedVariation.weight x)) -
          ∫ u in (0 : ℝ)..width x, discrepancy (x + u) - discrepancy x := by
      rw [← hsub]
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ Icc (0 : ℝ) (width x) := by
        simpa [uIcc_of_le hw0.le] using hu
      have hratio : weightRatio x (u / width x) =
          MellinWeightedVariation.weight (x + u) /
            MellinWeightedVariation.weight x := by
        unfold weightRatio
        congr 2
        field_simp
      change (discrepancy (x + u) - discrepancy x) *
        (weightRatio x (u / width x) - 1) =
        (discrepancy (x + u) - discrepancy x) *
          (MellinWeightedVariation.weight (x + u) /
            MellinWeightedVariation.weight x) -
          (discrepancy (x + u) - discrepancy x)
      rw [hratio]
      ring
    unfold forwardResponse unweightedResponse triangularAverage triangularPrimitive
    simp only [VarianceTransferDefs.increment]
    rw [hsub']
    ring
  rw [hdiff_eq]
  have hbound_u : ∀ u ∈ Set.uIoc (0 : ℝ) (width x),
      |(discrepancy (x + u) - discrepancy x) *
          (weightRatio x (u / width x) - 1)| ≤
        (C * Real.sqrt x * (Real.log x) ^ 2) * (4 * x ^ (-1 / 5 : ℝ)) := by
    intro u hu
    have hu' : u ∈ Ioc (0 : ℝ) (width x) := by
      simpa [uIoc_of_le hw0.le] using hu
    have hu0 : 0 ≤ u := hu'.1.le
    have huw : u ≤ width x := hu'.2
    have hratio := weightRatio_sub_one hx4 (div_nonneg hu0 hw0.le)
      (show u / width x ≤ 1 from (div_le_one hw0).2 huw)
    have hi := hxu u ⟨hu0, huw⟩
    rw [abs_mul]
    exact mul_le_mul (hxu u ⟨hu0, huw⟩) hratio (by positivity) (by positivity)
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun u : ℝ => (discrepancy (x + u) - discrepancy x) *
      (weightRatio x (u / width x) - 1))
    (C := (C * Real.sqrt x * (Real.log x) ^ 2) * (4 * x ^ (-1 / 5 : ℝ)))
    (by simpa only [Real.norm_eq_abs] using hbound_u)
  have hlen : |(width x) - 0| = width x := by
    rw [sub_zero]
    exact abs_of_pos hw0
  rw [hlen] at hint
  have hmain : |Real.sqrt x / width x ^ 2| *
      ((C * Real.sqrt x * (Real.log x) ^ 2) * (4 * x ^ (-1 / 5 : ℝ)) * width x) ≤
      4 * C * (Real.log x) ^ 2 := by
    rw [abs_of_nonneg (div_nonneg (Real.sqrt_nonneg x) (sq_nonneg _))]
    have hp : x * x ^ (-1 / 5 : ℝ) = width x := by
      unfold width
      conv_lhs => lhs; rw [← Real.rpow_one x]
      rw [← Real.rpow_add hx0]
      norm_num
    have hs : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    calc
      _ = (4 * C * (Real.log x) ^ 2) *
          (Real.sqrt x * Real.sqrt x) * x ^ (-1 / 5 : ℝ) / width x := by
        field_simp
      _ = 4 * C * (Real.log x) ^ 2 := by
        rw [hs, mul_assoc _ x, hp, mul_div_cancel_right₀ _ hw0.ne']
      _ ≤ _ := le_rfl
  calc
    |Real.sqrt x / width x ^ 2 *
        ∫ u in (0 : ℝ)..width x,
          (discrepancy (x + u) - discrepancy x) *
            (weightRatio x (u / width x) - 1)| =
      |Real.sqrt x / width x ^ 2| *
        |∫ u in (0 : ℝ)..width x,
          (discrepancy (x + u) - discrepancy x) *
            (weightRatio x (u / width x) - 1)| := abs_mul _ _
    _ ≤ 4 * C * (Real.log x) ^ 2 := by
      exact (mul_le_mul_of_nonneg_left hint (abs_nonneg _)).trans hmain

theorem forward_kernel_weight_removal_l2 (hVK : VonKochBound) :
    Filter.Tendsto
      (fun X => (∫ x in X..(2 * X), (forwardResponse x - unweightedResponse x) ^ 2 / x) /
        meanSquareScale X)
      Filter.atTop (nhds 0) := by
  obtain ⟨C, hbound⟩ := (forward_kernel_weight_removal hVK).bound
  let K := |C|
  have hK : 0 ≤ K := abs_nonneg C
  have hbound' : ∀ᶠ x : ℝ in atTop,
      |forwardResponse x - unweightedResponse x| ≤ K * (Real.log x) ^ 2 := by
    filter_upwards [hbound] with x hx
    simp only [Real.norm_eq_abs, abs_pow, sq_abs] at hx
    exact hx.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg _))
  obtain ⟨Y, hY⟩ := eventually_atTop.mp hbound'
  have hdecay : Tendsto (fun X : ℝ =>
      16 * K ^ 2 * ((Real.log X) ^ 3 / X ^ (1 / 5 : ℝ))) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (3 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 5)).tendsto_div_nhds_zero
    simpa only [Real.rpow_ofNat, mul_zero] using h.const_mul (16 * K ^ 2)
  apply squeeze_zero' ?_ ?_ hdecay
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX
    have hX0 : 0 < X := by linarith
    have hscale : 0 < meanSquareScale X := by
      exact mul_pos (Real.rpow_pos_of_pos hX0 _) (Real.log_pos (by linarith))
    apply div_nonneg _ hscale.le
    apply intervalIntegral.integral_nonneg (by linarith : X ≤ 2 * X)
    intro x hx
    exact div_nonneg (sq_nonneg _) (by linarith [hx.1])
  · filter_upwards [eventually_ge_atTop (max 2 Y)] with X hX
    have hX2 : 2 ≤ X := (le_max_left _ _).trans hX
    have hXY : Y ≤ X := (le_max_right _ _).trans hX
    have hX0 : 0 < X := by linarith
    have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
    have hscale : 0 < meanSquareScale X :=
      mul_pos (Real.rpow_pos_of_pos hX0 _) hlogX
    have hpoint (x : ℝ) (hx : x ∈ Icc X (2 * X)) :
        |(forwardResponse x - unweightedResponse x) ^ 2 / x| ≤
          16 * K ^ 2 * (Real.log X) ^ 4 / X := by
      have hx0 : 0 < x := hX0.trans_le hx.1
      have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith [hx.1])
      have hlog : Real.log x ≤ 2 * Real.log X := by
        have h := Real.log_le_log hx0 hx.2
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hX0.ne'] at h
        have h2 : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX2
        linarith
      have habs : |forwardResponse x - unweightedResponse x| ≤
          4 * K * (Real.log X) ^ 2 := by
        calc
          _ ≤ K * (Real.log x) ^ 2 := hY x (hXY.trans hx.1)
          _ ≤ K * (2 * Real.log X) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogx hlog 2) hK
          _ = _ := by ring
      have hs : (forwardResponse x - unweightedResponse x) ^ 2 ≤
          16 * K ^ 2 * (Real.log X) ^ 4 := by
        calc
          _ = |forwardResponse x - unweightedResponse x| ^ 2 := (sq_abs _).symm
          _ ≤ (4 * K * (Real.log X) ^ 2) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) habs 2
          _ = _ := by ring
      rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hx0.le)]
      exact (div_le_div_of_nonneg_right hs hx0.le).trans
        (div_le_div_of_nonneg_left (by positivity) hX0 hx.1)
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := X) (b := 2 * X)
      (f := fun x : ℝ => (forwardResponse x - unweightedResponse x) ^ 2 / x)
      (C := 16 * K ^ 2 * (Real.log X) ^ 4 / X) (by
        intro x hx
        have hx' : x ∈ Icc X (2 * X) := by
          have hXX : X ≤ 2 * X := by linarith
          exact Ioc_subset_Icc_self (by simpa only [uIoc_of_le hXX] using hx)
        simpa only [Real.norm_eq_abs] using hpoint x hx')
    have hi' : (∫ x in X..(2 * X),
        (forwardResponse x - unweightedResponse x) ^ 2 / x) ≤
          16 * K ^ 2 * (Real.log X) ^ 4 := by
      calc
        _ ≤ |∫ x in X..(2 * X),
            (forwardResponse x - unweightedResponse x) ^ 2 / x| := le_abs_self _
        _ ≤ (16 * K ^ 2 * (Real.log X) ^ 4 / X) * |2 * X - X| := hi
        _ = _ := by rw [show 2 * X - X = X by ring, abs_of_pos hX0]; field_simp
    calc
      _ ≤ (16 * K ^ 2 * (Real.log X) ^ 4) / meanSquareScale X :=
        div_le_div_of_nonneg_right hi' hscale.le
      _ = 16 * K ^ 2 * ((Real.log X) ^ 3 / X ^ (1 / 5 : ℝ)) := by
        unfold meanSquareScale
        field_simp

end
end D5.S3.Arith.Robin.ForwardKernel.WeightRemoval
