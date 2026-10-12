/- GID: D5/S3/Arith/Robin/OriginalMovingWindowMoment
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/OriginalMovingWindowMoment
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: The original reciprocal-logarithmic moving window has explicit decaying moment bounds. -/

import D5.S3.Arith.Robin.MellinWeightedVariation
import D5.S3.Arith.Robin.ActualRobinClockCovariance
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set
open D5.S3.Arith.Robin.MellinWeightedVariation (weight)
open D5.S3.Arith.Robin.ActualRobinClockCovariance (g activationDensity)

namespace D5.S3.Arith.Robin.OriginalMovingWindowMoment

def width (t : ℝ) : ℝ := t ^ (4 / 5 : ℝ)
def endpoint (t : ℝ) : ℝ := t + width t

/-- Strict initial exclusion and weak terminal inclusion of the original kernel. -/
def kernel (t x : ℝ) : ℝ :=
  if t < x ∧ x ≤ endpoint t then
    (g x - g (endpoint t)) / (weight t * t ^ (11 / 10 : ℝ))
  else 0

def moment (t β : ℝ) : ℝ :=
  ∫ x in t..endpoint t, kernel t x * (x - 2) ^ (-β)

private lemma weight_pos {x : ℝ} (hx : 1 < x) : 0 < weight x := by
  unfold weight
  positivity [Real.log_pos hx]

private lemma weight_continuous {a b : ℝ} (ha : 1 < a) :
    ContinuousOn weight (Icc a b) := by
  intro x hx
  have hx1 := ha.trans_le hx.1
  have hx0 : 0 < x := by linarith
  have hl := Real.log_pos hx1
  exact ((Real.continuousAt_log hx0.ne').add continuousAt_const).div
    ((continuousAt_id.pow 2).mul ((Real.continuousAt_log hx0.ne').pow 2))
    (mul_ne_zero (pow_ne_zero 2 hx0.ne') (pow_ne_zero 2 hl.ne'))
    |>.continuousWithinAt

private lemma log_large {x : ℝ} (hx : 4 ≤ x) : 1 ≤ Real.log x := by
  have h := Real.log_pow (2 : ℝ) 2
  norm_num at h
  have h2 := Real.log_two_gt_d9
  have h4 : 1 ≤ Real.log (4 : ℝ) := by linarith
  exact h4.trans (Real.log_le_log (by norm_num) hx)

private lemma weight_antitone {t y : ℝ} (ht : 1 < t) (hty : t ≤ y) :
    weight y ≤ weight t := by
  have ht0 : 0 < t := by linarith
  have hscaled := MellinWeightedVariation.scaleWeight_antitone
    (x := t) (y := 1) (a := t) (b := y) ht (by norm_num) ht0 hty (by simp)
  rw [MellinWeightedVariation.scaleWeight_eq,
    MellinWeightedVariation.scaleWeight_eq, mul_one, mul_one] at hscaled
  have hnormalize := mul_le_mul_of_nonneg_right hty
    (weight_pos (ht.trans_le hty)).le
  exact (mul_le_mul_iff_right₀ ht0).mp (hnormalize.trans hscaled)

private lemma weight_ratio_lower {t y : ℝ} (ht : 4 ≤ t) (hty : t ≤ y) :
    (t / y) ^ 4 * weight t ≤ weight y := by
  have ht0 : 0 < t := by linarith
  have hy0 : 0 < y := ht0.trans_le hty
  have hl := Real.log_pos (show 1 < t by linarith)
  have hly := Real.log_pos (show 1 < y by linarith)
  have hlog := Real.log_le_log ht0 hty
  have hquot : 1 ≤ y / t := (one_le_div ht0).mpr hty
  have hgrowth := Real.log_le_sub_one_of_pos (div_pos hy0 ht0)
  rw [Real.log_div hy0.ne' ht0.ne'] at hgrowth
  have hlinear : Real.log y ≤ y / t * Real.log t := by
    have h := mul_nonneg (sub_nonneg.mpr hquot) (sub_nonneg.mpr (log_large ht))
    nlinarith
  have hsquare : (Real.log y) ^ 2 ≤ (y / t * Real.log t) ^ 2 := by
    nlinarith
  unfold weight
  apply (le_div_iff₀ (by positivity : 0 < y ^ 2 * Real.log y ^ 2)).2
  have hscaled : (t / y) ^ 4 * ((Real.log t + 1) / (t ^ 2 * Real.log t ^ 2)) *
      (y ^ 2 * Real.log y ^ 2) ≤ Real.log t + 1 := by
    calc
      _ ≤ (t / y) ^ 4 * ((Real.log t + 1) / (t ^ 2 * Real.log t ^ 2)) *
          (y ^ 2 * (y / t * Real.log t) ^ 2) := by gcongr
      _ = _ := by field_simp [ht0.ne', hy0.ne', hl.ne'] <;> ring
  exact hscaled.trans (by linarith)

private lemma price_drop {t x b : ℝ} (ht : 4 ≤ t) (htx : t ≤ x) (hxb : x ≤ b) :
    weight b * (b - x) ≤ g x - g b ∧
      g x - g b ≤ weight t * (b - x) := by
  have hx1 : 1 < x := by linarith
  have hb1 : 1 < b := by linarith
  have hw : IntervalIntegrable weight volume x b := (show ContinuousOn weight (uIcc x b) by
    rw [uIcc_of_le hxb]; exact weight_continuous hx1).intervalIntegrable
  have heq : (∫ y in x..b, weight y) = g x - g b :=
    ActualRobinClockCovariance.density_integral hx1 hxb
  constructor
  · calc
      _ = ∫ _y in x..b, weight b := by simp; ring
      _ ≤ ∫ y in x..b, weight y :=
        intervalIntegral.integral_mono_on hxb intervalIntegrable_const hw
          (fun y hy => weight_antitone (by linarith [hy.1] : 1 < y) hy.2)
      _ = _ := heq
  · calc
      _ = ∫ y in x..b, weight y := heq.symm
      _ ≤ ∫ _y in x..b, weight t :=
        intervalIntegral.integral_mono_on hxb hw intervalIntegrable_const
          (fun y hy => weight_antitone (by linarith) (htx.trans hy.1))
      _ = _ := by simp; ring

private lemma body_continuous {t b β : ℝ} (ht : 4 ≤ t) :
    ContinuousOn (fun x => (g x - g b) * (x - 2) ^ (-β)) (Icc t b) := by
  have hp : ContinuousOn g (Icc t b) := by
    intro x hx
    exact (ActualRobinClockCovariance.g_has_deriv_at
      (by linarith [hx.1] : 1 < x)).continuousAt.continuousWithinAt
  exact (hp.sub continuousOn_const).mul
    ((continuousOn_id.sub continuousOn_const).rpow_const
      (fun x hx => Or.inl (by linarith [hx.1] : x - 2 ≠ 0)))

private lemma triangle_integral (t b C : ℝ) :
    (∫ x in t..b, C * (b - x)) = C * (b - t) ^ 2 / 2 := by
  have hi : (∫ x in t..b, b - x) = (b - t) * b - (b ^ 2 - t ^ 2) / 2 := by
    simpa only [Pi.sub_apply, id_eq, intervalIntegral.integral_const, integral_id, smul_eq_mul]
      using! (intervalIntegral.integral_sub (f := fun _ : ℝ => b) (g := fun x : ℝ => x)
        (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => b) volume t b)
        (continuous_id.intervalIntegrable t b))
  rw [intervalIntegral.integral_const_mul, hi]
  ring

/-- The literal price-difference kernel, rather than a replacement triangle,
has a moment squeezed by its exact endpoint weight and endpoint observations. -/
private theorem endpoint_moment_bounds {t β : ℝ} (ht : 4 ≤ t) (hβ : 0 ≤ β) :
    (t / endpoint t) ^ 4 * (endpoint t - 2) ^ (-β) *
        width t ^ 2 / (2 * t ^ (11 / 10 : ℝ)) ≤ moment t β ∧
    moment t β ≤ (t - 2) ^ (-β) * width t ^ 2 / (2 * t ^ (11 / 10 : ℝ)) := by
  have ht0 : 0 < t := by linarith
  have hh : 0 < width t := Real.rpow_pos_of_pos ht0 _
  have htb : t ≤ endpoint t := by dsimp [endpoint]; linarith
  have hb0 : 0 < endpoint t := ht0.trans_le htb
  have hw0 := weight_pos (show 1 < t by linarith)
  have hden : 0 < weight t * t ^ (11 / 10 : ℝ) := by positivity
  have hbody : IntervalIntegrable
      (fun x => (g x - g (endpoint t)) * (x - 2) ^ (-β)) volume t (endpoint t) := (show ContinuousOn
      (fun x => (g x - g (endpoint t)) * (x - 2) ^ (-β))
      (uIcc t (endpoint t)) by
    rw [uIcc_of_le htb]; exact body_continuous ht).intervalIntegrable
  have heq : moment t β = (∫ x in t..endpoint t,
      (g x - g (endpoint t)) * (x - 2) ^ (-β)) /
        (weight t * t ^ (11 / 10 : ℝ)) := by
    unfold moment
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with x hx
    rw [uIoc_of_le htb] at hx
    unfold kernel
    rw [if_pos (show t < x ∧ x ≤ endpoint t from hx)]
    ring
  have hlo : ∀ x ∈ Icc t (endpoint t),
      weight (endpoint t) * (endpoint t - 2) ^ (-β) * (endpoint t - x) ≤
        (g x - g (endpoint t)) * (x - 2) ^ (-β) := by
    intro x hx
    have hd := price_drop ht hx.1 hx.2
    have hp := Real.rpow_le_rpow_of_nonpos (by linarith [hx.1] : 0 < x - 2)
      (by linarith [hx.2] : x - 2 ≤ endpoint t - 2) (by linarith : -β ≤ 0)
    have h := mul_le_mul hd.1 hp
      (Real.rpow_nonneg (by linarith : 0 ≤ endpoint t - 2) _)
      ((mul_nonneg (weight_pos (by linarith : 1 < endpoint t)).le
        (sub_nonneg.mpr hx.2)).trans hd.1)
    simpa only [mul_assoc, mul_comm, mul_left_comm] using! h
  have hhi : ∀ x ∈ Icc t (endpoint t),
      (g x - g (endpoint t)) * (x - 2) ^ (-β) ≤
        weight t * (t - 2) ^ (-β) * (endpoint t - x) := by
    intro x hx
    have hd := price_drop ht hx.1 hx.2
    have hp := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < t - 2)
      (by linarith [hx.1] : t - 2 ≤ x - 2) (by linarith : -β ≤ 0)
    have h := mul_le_mul hd.2 hp (Real.rpow_nonneg (by linarith [hx.1] : 0 ≤ x - 2) _)
      (mul_nonneg hw0.le (sub_nonneg.mpr hx.2))
    simpa only [mul_assoc, mul_comm, mul_left_comm] using! h
  have hilow : IntervalIntegrable (fun x =>
      weight (endpoint t) * (endpoint t - 2) ^ (-β) * (endpoint t - x)) volume t (endpoint t) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hihigh : IntervalIntegrable (fun x =>
      weight t * (t - 2) ^ (-β) * (endpoint t - x)) volume t (endpoint t) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hl := intervalIntegral.integral_mono_on htb hilow hbody hlo
  have hu := intervalIntegral.integral_mono_on htb hbody hihigh hhi
  rw [triangle_integral, show endpoint t - t = width t by simp [endpoint]] at hl hu
  have hr := weight_ratio_lower ht htb
  rw [heq]
  constructor
  · apply (le_div_iff₀ hden).2
    calc
      _ ≤ weight (endpoint t) * (endpoint t - 2) ^ (-β) * width t ^ 2 / 2 := by
        calc
          _ = ((t / endpoint t) ^ 4 * weight t) *
              ((endpoint t - 2) ^ (-β) * width t ^ 2 / 2) := by
            field_simp [(Real.rpow_pos_of_pos ht0 (11 / 10 : ℝ)).ne']
            <;> ring
          _ ≤ weight (endpoint t) *
              ((endpoint t - 2) ^ (-β) * width t ^ 2 / 2) :=
            mul_le_mul_of_nonneg_right hr
              (div_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ endpoint t - 2) _)
                (sq_nonneg (width t))) (by norm_num))
          _ = _ := by ring
      _ ≤ _ := hl
  · apply (div_le_iff₀ hden).2
    convert hu using 1 <;> first | rfl |
      (field_simp [(Real.rpow_pos_of_pos ht0 (11 / 10 : ℝ)).ne'] <;> ring)

private lemma negative_power_lower {δ c : ℝ} (hδ : 0 ≤ δ) (hc : 0 ≤ c) :
    1 - c * δ ≤ (1 + δ) ^ (-c) := by
  have hd : ∀ x ∈ Icc (1 : ℝ) (1 + δ), HasDerivAt
      (fun y : ℝ => y ^ (-c) + c * y)
      (-c * x ^ (-c - 1) + c) x := by
    intro x hx
    simpa only [id_eq, mul_one] using!
      (Real.hasDerivAt_rpow_const (p := -c) (Or.inl (by linarith [hx.1] : x ≠ 0))).add
        ((hasDerivAt_id x).const_mul c)
  have hn : ∀ x ∈ Icc (1 : ℝ) (1 + δ), 0 ≤ -c * x ^ (-c - 1) + c := by
    intro x hx
    have hp := Real.rpow_le_rpow_of_nonpos zero_lt_one hx.1
      (show -c - 1 ≤ 0 by linarith)
    rw [Real.one_rpow] at hp
    nlinarith
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 1 (1 + δ))
    (HasDerivAt.continuousOn hd)
    (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => hn x (interior_subset hx))
  have h := hm (left_mem_Icc.mpr (by linarith))
    (right_mem_Icc.mpr (by linarith)) (by linarith)
  simp only [Real.one_rpow, mul_one] at h
  linarith

private lemma negative_power_upper {z c : ℝ} (hz : (1 / 2 : ℝ) ≤ z)
    (hz1 : z ≤ 1) (hc : 0 ≤ c) :
    z ^ (-c) ≤ 1 + c * 2 ^ (c + 1) * (1 - z) := by
  let C : ℝ := c * 2 ^ (c + 1)
  have hd : ∀ x ∈ Icc z 1, HasDerivAt
      (fun y : ℝ => y ^ (-c) + C * y)
      (-c * x ^ (-c - 1) + C) x := by
    intro x hx
    simpa only [id_eq, mul_one] using!
      (Real.hasDerivAt_rpow_const (p := -c) (Or.inl (by linarith [hx.1] : x ≠ 0))).add
        ((hasDerivAt_id x).const_mul C)
  have hn : ∀ x ∈ Icc z 1, 0 ≤ -c * x ^ (-c - 1) + C := by
    intro x hx
    have hp := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1 / 2)
      (hz.trans hx.1) (show -c - 1 ≤ 0 by linarith)
    have heq : (1 / 2 : ℝ) ^ (-c - 1) = (2 : ℝ) ^ (c + 1) := by
      rw [show -c - 1 = -(c + 1) by ring, Real.rpow_neg_eq_inv_rpow]
      norm_num
    rw [heq] at hp
    dsimp [C]
    nlinarith
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc z 1)
    (HasDerivAt.continuousOn hd)
    (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => hn x (interior_subset hx))
  have h := hm (left_mem_Icc.mpr hz1) (right_mem_Icc.mpr hz1) hz1
  simp only [Real.one_rpow, mul_one] at h
  dsimp [C] at h
  nlinarith

private lemma width_scale {t : ℝ} (ht : 0 < t) :
    width t ^ 2 / t ^ (11 / 10 : ℝ) = t ^ (1 / 2 : ℝ) := by
  unfold width
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← Real.rpow_sub ht]
  norm_num

/-- Uniform quantitative control of the exact original continuous moment.
The bound is valid for every source window with t ≥ 4; no selected family is thinned. -/
theorem original_window_moment_estimate {t β : ℝ} (ht : 4 ≤ t) (hβ : 0 ≤ β) :
    |moment t β - t ^ (1 / 2 - β) / 2| ≤
      (4 + β + 2 * β * 2 ^ (β + 1)) * t ^ (-1 / 5 : ℝ) *
        (t ^ (1 / 2 - β) / 2) := by
  have ht0 : 0 < t := by linarith
  have ht1 : 1 ≤ t := by linarith
  have htb : t ≤ endpoint t := by
    dsimp [endpoint, width]
    exact le_add_of_nonneg_right (Real.rpow_nonneg ht0.le _)
  have hb0 := ht0.trans_le htb
  let δ : ℝ := t ^ (-1 / 5 : ℝ)
  let A : ℝ := t ^ (1 / 2 - β) / 2
  have hδ : 0 ≤ δ := Real.rpow_nonneg ht0.le _
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : endpoint t = t * (1 + δ) := by
    have h : width t = t * δ := by
      dsimp [width, δ]
      simpa only [show (1 : ℝ) + -1 / 5 = 4 / 5 by norm_num, Real.rpow_one]
        using (Real.rpow_add ht0 (1 : ℝ) (-1 / 5 : ℝ))
    dsimp [endpoint]
    rw [h]
    ring
  have heq : t ^ (-β) * width t ^ 2 / (2 * t ^ (11 / 10 : ℝ)) = A := by
    dsimp [A]
    rw [show t ^ (-β) * width t ^ 2 / (2 * t ^ (11 / 10 : ℝ)) =
      (width t ^ 2 / t ^ (11 / 10 : ℝ)) * t ^ (-β) / 2 by ring,
      width_scale ht0, ← Real.rpow_add ht0]
    congr 2
  have hlo : (1 + δ) ^ (-(4 + β)) * A ≤ moment t β := by
    have hp := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < endpoint t - 2)
      (show endpoint t - 2 ≤ endpoint t by linarith) (by linarith : -β ≤ 0)
    have h := (mul_le_mul_of_nonneg_left hp
      (show 0 ≤ (t / endpoint t) ^ 4 by positivity))
    have h' := mul_le_mul_of_nonneg_right h
      (show 0 ≤ width t ^ 2 / (2 * t ^ (11 / 10 : ℝ)) by positivity)
    have hbound := endpoint_moment_bounds ht hβ
    have he : (t / endpoint t) ^ 4 * endpoint t ^ (-β) *
        (width t ^ 2 / (2 * t ^ (11 / 10 : ℝ))) = (1 + δ) ^ (-(4 + β)) * A := by
      have hbpower : endpoint t ^ (-β) = t ^ (-β) * (1 + δ) ^ (-β) := by
        rw [hB, Real.mul_rpow ht0.le (by positivity)]
      have hd : t / (t * (1 + δ)) = (1 + δ)⁻¹ := by
        field_simp [ht0.ne'] <;> ring
      have hratio : (t / endpoint t) ^ 4 = (1 + δ) ^ (-4 : ℝ) := by
        rw [hB, hd, ← Real.rpow_natCast, Real.inv_rpow (by positivity),
          Real.rpow_neg (by positivity)]
        norm_num
      rw [hratio, hbpower, show -(4 + β) = (-4 : ℝ) + -β by ring,
        Real.rpow_add (by positivity)]
      rw [← heq]
      ring
    rw [he] at h'
    exact h'.trans (by simpa only [mul_div_assoc] using! hbound.1)
  have hhi : moment t β ≤ (1 - 2 / t) ^ (-β) * A := by
    have hz : 0 < 1 - 2 / t := by
      have h : 2 / t ≤ (1 / 2 : ℝ) := (div_le_iff₀ ht0).2 (by linarith)
      linarith
    have he : t - 2 = t * (1 - 2 / t) := by field_simp [ht0.ne'] <;> ring
    have h := (endpoint_moment_bounds ht hβ).2
    rw [he, Real.mul_rpow ht0.le hz.le] at h
    calc
      _ ≤ _ := h
      _ = _ := by rw [← heq]; ring
  have hlow := mul_le_mul_of_nonneg_right
    (negative_power_lower hδ (show 0 ≤ 4 + β by linarith)) hA.le
  have hsmall : (1 / 2 : ℝ) ≤ 1 - 2 / t := by
    have h : 2 / t ≤ (1 / 2 : ℝ) := (div_le_iff₀ ht0).2 (by linarith)
    linarith
  have hz1 : 1 - 2 / t ≤ 1 := sub_le_self _ (by positivity)
  have hu := mul_le_mul_of_nonneg_right (negative_power_upper hsmall hz1 hβ) hA.le
  have hrecip : 1 / t ≤ δ := by
    dsimp [δ]
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
  rw [abs_le]
  change -((4 + β + 2 * β * 2 ^ (β + 1)) * δ * A) ≤ moment t β - A ∧
    moment t β - A ≤ (4 + β + 2 * β * 2 ^ (β + 1)) * δ * A
  have hextra0 : 0 ≤ 2 * β * 2 ^ (β + 1) * δ * A := by positivity
  have hbase0 : 0 ≤ (4 + β) * δ * A := by positivity
  constructor
  · nlinarith [hlow.trans hlo]
  · have hc : 0 ≤ β * 2 ^ (β + 1) := by positivity
    have hextra := mul_le_mul_of_nonneg_right hrecip
      (show 0 ≤ 2 * (β * 2 ^ (β + 1)) * A by positivity)
    have hup : moment t β ≤ A + 2 * (β * 2 ^ (β + 1)) * A * (1 / t) := by
      convert hhi.trans hu using 1 <;> first | rfl | ring
    have hpaid : 2 * (β * 2 ^ (β + 1)) * A * (1 / t) ≤
        2 * β * 2 ^ (β + 1) * δ * A := by
      convert hextra using 1 <;> first | rfl | ring
    nlinarith only [hup, hpaid, hbase0]

open scoped ENNReal NNReal BigOperators

/-- The right-limit height at the strict lower end of the original window. -/
def lowerHeight (t : ℝ) : ℝ :=
  (g t - g (endpoint t)) / (weight t * t ^ (11 / 10 : ℝ))

/-- The original window averaged over the complete reference interval. -/
def windowMass (ell R x : ℝ) : ℝ := ∫ s in Icc ell R, kernel s x

/-- The part of that same mass before the actual divisor activation clock. -/
def beforeMass (ell R : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
  ∫ s in Icc ell R ∩ Iio ((d : ℝ) ^ (500 / 151 : ℝ)), kernel s x

/-- The ratio is zero when the normalizer vanishes. -/
def beforeRatio (ell R : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
  beforeMass ell R d x / windowMass ell R x

/-- The weighted moving-cut discrepancy on its literal integer row. -/
def cutRow (ell R t : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
  Real.log (x / d) * kernel t x *
    ((if t < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0) - beforeRatio ell R d x)

private lemma endpoint_le_twice {t : ℝ} (ht : 1 ≤ t) : endpoint t ≤ 2 * t := by
  have hw : width t ≤ t := by
    unfold width
    simpa using Real.rpow_le_rpow_of_exponent_le ht (by norm_num : (4 / 5 : ℝ) ≤ 1)
  dsimp [endpoint]
  linarith

private lemma endpoint_strictMonoOn : StrictMonoOn endpoint (Ici (1 : ℝ)) := by
  intro s hs t ht hst
  change 1 ≤ s at hs
  change 1 ≤ t at ht
  have hw : width s ≤ width t := Real.rpow_le_rpow (by linarith [hs] : 0 ≤ s)
    hst.le (by norm_num)
  dsimp [endpoint]
  linarith

private lemma kernel_nonneg {t x : ℝ} (ht : 4 ≤ t) : 0 ≤ kernel t x := by
  have hden : 0 < weight t * t ^ (11 / 10 : ℝ) :=
    mul_pos (weight_pos (by linarith)) (Real.rpow_pos_of_pos (by linarith) _)
  unfold kernel
  split_ifs with hx
  · apply div_nonneg _ hden.le
    have h := (price_drop ht hx.1.le hx.2).1
    have hwb : 0 ≤ weight (endpoint t) := (weight_pos (by linarith [hx.1, hx.2])).le
    exact (mul_nonneg hwb (sub_nonneg.mpr hx.2)).trans h
  · exact le_rfl

private lemma height_bounds {t : ℝ} (ht : 4 ≤ t) :
    0 ≤ lowerHeight t ∧ lowerHeight t ≤ t ^ (-3 / 10 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have htb : t ≤ endpoint t := le_add_of_nonneg_right (Real.rpow_nonneg ht0.le _)
  have hw := weight_pos (by linarith : 1 < t)
  have hp := price_drop ht (le_refl t) htb
  have hden := mul_pos hw (Real.rpow_pos_of_pos ht0 (11 / 10 : ℝ))
  constructor
  · exact div_nonneg ((mul_nonneg (weight_pos (by linarith : 1 < endpoint t)).le
      (sub_nonneg.mpr htb)).trans hp.1) hden.le
  · unfold lowerHeight
    apply (div_le_iff₀ hden).2
    calc
      _ ≤ weight t * width t := by simpa [endpoint] using hp.2
      _ = t ^ (-3 / 10 : ℝ) * (weight t * t ^ (11 / 10 : ℝ)) := by
        unfold width
        rw [show t ^ (-3 / 10 : ℝ) * (weight t * t ^ (11 / 10 : ℝ)) =
          weight t * (t ^ (-3 / 10 : ℝ) * t ^ (11 / 10 : ℝ)) by ring,
          ← Real.rpow_add ht0]
        norm_num

private lemma kernel_le_height {t x : ℝ} (ht : 4 ≤ t) :
    kernel t x ≤ lowerHeight t := by
  have ht0 : 0 < t := by linarith
  have hden := mul_pos (weight_pos (by linarith : 1 < t))
    (Real.rpow_pos_of_pos ht0 (11 / 10 : ℝ))
  unfold kernel
  split_ifs with hx
  · apply (div_le_div_iff_of_pos_right hden).2
    have h := (price_drop ht (le_refl t) hx.1.le).1
    have hw := weight_pos (by linarith [hx.1] : 1 < x)
    linarith [mul_nonneg hw.le (sub_nonneg.mpr hx.1.le)]
  · exact (height_bounds ht).1

private lemma kernel_pos_iff {t x : ℝ} (ht : 4 ≤ t) :
    0 < kernel t x ↔ t < x ∧ x < endpoint t := by
  have ht0 : 0 < t := by linarith
  have hden := mul_pos (weight_pos (by linarith : 1 < t))
    (Real.rpow_pos_of_pos ht0 (11 / 10 : ℝ))
  unfold kernel
  constructor
  · intro h
    split_ifs at h with hx
    · refine ⟨hx.1, hx.2.lt_of_ne ?_⟩
      intro he
      simpa [he] using h
    · exact (lt_irrefl _ h).elim
  · rintro ⟨hx, hxb⟩
    rw [if_pos ⟨hx, hxb.le⟩]
    apply div_pos _ hden
    exact (mul_pos (weight_pos (by linarith : 1 < endpoint t))
      (sub_pos.mpr hxb)).trans_le (price_drop ht hx.le hxb.le).1

private lemma kernel_zero_of_outside {t x : ℝ}
    (hx : x ≤ t ∨ endpoint t ≤ x) : kernel t x = 0 := by
  unfold kernel
  rcases hx with hx | hx
  · rw [if_neg (by simp [not_lt.mpr hx])]
  · by_cases he : x = endpoint t
    · simp [he]
    · rw [if_neg (by grind)]

private lemma kernel_le_one {t x : ℝ} (ht : 4 ≤ t) : kernel t x ≤ 1 := by
  exact (kernel_le_height ht).trans ((height_bounds ht).2.trans
    (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)))

private lemma measurable_kernel_left (x : ℝ) : Measurable (fun t : ℝ => kernel t x) := by
  unfold kernel g weight endpoint width
  apply Measurable.ite
  · exact (measurableSet_lt measurable_id measurable_const).inter
      (measurableSet_le measurable_const
        (show Measurable (fun t : ℝ => t + t ^ (4 / 5 : ℝ)) from
          (continuous_id.add (Real.continuous_rpow_const (by norm_num))).measurable))
  · fun_prop
  · exact measurable_const

private lemma kernel_integrableOn {ell R x : ℝ} (hell : 4 ≤ ell) :
    IntegrableOn (fun t => kernel t x) (Icc ell R) := by
  apply (integrableOn_const (C := (1 : ℝ)) (by simp : volume (Icc ell R) ≠ ⊤)).mono'
    (measurable_kernel_left x).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg (hell.trans ht.1))]
  exact kernel_le_one (hell.trans ht.1)

private lemma kernel_cross_product {s t x y : ℝ}
    (hs : 4 ≤ s) (hst : s ≤ t) (hx : 4 ≤ x) (hxy : x ≤ y) :
    kernel s y * kernel t x ≤ kernel s x * kernel t y := by
  have ht : 4 ≤ t := hs.trans hst
  have hn : 0 ≤ kernel s x * kernel t y := mul_nonneg (kernel_nonneg hs) (kernel_nonneg ht)
  by_cases hsy : s < y ∧ y ≤ endpoint s
  · by_cases htx : t < x ∧ x ≤ endpoint t
    · have hB : endpoint s ≤ endpoint t :=
        endpoint_strictMonoOn.monotoneOn (by simpa using (show 1 ≤ s by linarith))
          (by simpa using (show 1 ≤ t by linarith)) hst
      have hsx : s < x ∧ x ≤ endpoint s := ⟨lt_of_le_of_lt hst htx.1, hxy.trans hsy.2⟩
      have hty : t < y ∧ y ≤ endpoint t := ⟨htx.1.trans_le hxy, hsy.2.trans hB⟩
      have hs0 : 0 < weight s * s ^ (11 / 10 : ℝ) :=
        mul_pos (weight_pos (by linarith)) (Real.rpow_pos_of_pos (by linarith) _)
      have ht0 : 0 < weight t * t ^ (11 / 10 : ℝ) :=
        mul_pos (weight_pos (by linarith)) (Real.rpow_pos_of_pos (by linarith) _)
      have hgxy : 0 ≤ g x - g y := by
        have h := (price_drop hx (le_refl x) hxy).1
        exact (mul_nonneg (weight_pos (by linarith : 1 < y)).le
          (sub_nonneg.mpr hxy)).trans h
      have hgB : 0 ≤ g (endpoint s) - g (endpoint t) := by
        have hbs : 4 ≤ endpoint s := hs.trans
          (le_add_of_nonneg_right (Real.rpow_nonneg (by linarith : 0 ≤ s) _))
        have h := (price_drop hbs (le_refl _) hB).1
        exact (mul_nonneg (weight_pos (by linarith : 1 < endpoint t)).le
          (sub_nonneg.mpr hB)).trans h
      simp only [kernel, if_pos hsy, if_pos htx, if_pos hsx, if_pos hty]
      rw [div_mul_div_comm, div_mul_div_comm]
      apply (div_le_div_iff_of_pos_right (mul_pos hs0 ht0)).2
      nlinarith [mul_nonneg hgxy hgB]
    · simpa only [kernel, if_neg htx, mul_zero] using hn
  · simpa only [kernel, if_neg hsy, zero_mul] using hn

private def afterMass (ell R : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
  ∫ s in Icc ell R \ Iio ((d : ℝ) ^ (500 / 151 : ℝ)), kernel s x

private lemma mass_split {ell R x : ℝ} (hell : 4 ≤ ell) (d : ℕ) :
    beforeMass ell R d x + afterMass ell R d x = windowMass ell R x :=
  integral_inter_add_sdiff measurableSet_Iio (kernel_integrableOn hell)

private lemma beforeRatio_bounds {ell R x : ℝ} (hell : 4 ≤ ell) (d : ℕ)
    (hK : 0 < windowMass ell R x) :
    0 ≤ beforeRatio ell R d x ∧ beforeRatio ell R d x ≤ 1 := by
  have hN : 0 ≤ beforeMass ell R d x := by
    apply setIntegral_nonneg (measurableSet_Icc.inter measurableSet_Iio)
    intro t ht
    exact kernel_nonneg (hell.trans ht.1.1)
  have hL : 0 ≤ afterMass ell R d x := by
    apply setIntegral_nonneg (measurableSet_Icc.diff measurableSet_Iio)
    intro t ht
    exact kernel_nonneg (hell.trans ht.1.1)
  constructor
  · exact div_nonneg hN hK.le
  · apply (div_le_one hK).2
    linarith [mass_split hell d (R := R) (x := x)]

private lemma beforeRatio_antitoneOn_positive {ell R x y : ℝ}
    (hell : 4 ≤ ell) (d : ℕ) (hx : 4 ≤ x) (hxy : x ≤ y)
    (hKx : 0 < windowMass ell R x) (hKy : 0 < windowMass ell R y) :
    beforeRatio ell R d y ≤ beforeRatio ell R d x := by
  let A := Icc ell R ∩ Iio ((d : ℝ) ^ (500 / 151 : ℝ))
  let L := Icc ell R \ Iio ((d : ℝ) ^ (500 / 151 : ℝ))
  have hAx : IntegrableOn (fun t => kernel t x) A :=
    (kernel_integrableOn hell).mono_set inter_subset_left
  have hAy : IntegrableOn (fun t => kernel t y) A :=
    (kernel_integrableOn hell).mono_set inter_subset_left
  have hLx : IntegrableOn (fun t => kernel t x) L :=
    (kernel_integrableOn hell).mono_set sdiff_subset
  have hLy : IntegrableOn (fun t => kernel t y) L :=
    (kernel_integrableOn hell).mono_set sdiff_subset
  have hpoint : ∀ s ∈ A,
      kernel s y * afterMass ell R d x ≤ kernel s x * afterMass ell R d y := by
    intro s hs
    dsimp [afterMass]
    rw [← integral_const_mul, ← integral_const_mul]
    apply setIntegral_mono_on (hLx.const_mul _) (hLy.const_mul _)
      (measurableSet_Icc.diff measurableSet_Iio)
    intro t ht
    exact kernel_cross_product (hell.trans hs.1.1)
      (show s ≤ t by dsimp [A, L] at hs ht; exact hs.2.le.trans (not_lt.mp ht.2)) hx hxy
  have hprod : beforeMass ell R d y * afterMass ell R d x ≤
      beforeMass ell R d x * afterMass ell R d y := by
    dsimp [beforeMass]
    rw [← integral_mul_const, ← integral_mul_const]
    exact setIntegral_mono_on (hAy.mul_const _) (hAx.mul_const _)
      (measurableSet_Icc.inter measurableSet_Iio) hpoint
  unfold beforeRatio
  apply (div_le_div_iff₀ hKy hKx).2
  rw [← mass_split hell d (x := x), ← mass_split hell d (x := y)]
  nlinarith only [hprod]

private lemma endpoint_continuous : Continuous endpoint :=
  continuous_id.add (Real.continuous_rpow_const (by norm_num))

private lemma windowMass_pos_of_kernel_pos {ell R t x : ℝ}
    (hell : 4 ≤ ell) (horder : ell < R) (ht : t ∈ Icc ell R)
    (hk : 0 < kernel t x) : 0 < windowMass ell R x := by
  let U : Set ℝ := {s | s < x ∧ x < endpoint s}
  have hU : IsOpen U := (isOpen_lt continuous_id continuous_const).inter
    (isOpen_lt continuous_const endpoint_continuous)
  have htU : t ∈ U := (kernel_pos_iff (hell.trans ht.1)).mp hk
  have htcl : t ∈ closure (Ioo ell R) := by
    rw [closure_Ioo horder.ne]
    exact ht
  have hne : (U ∩ Ioo ell R).Nonempty :=
    mem_closure_iff.mp htcl U hU htU
  have hp : 0 < volume (U ∩ Ioo ell R) := (hU.inter isOpen_Ioo).measure_pos volume hne
  have hsub : U ∩ Ioo ell R ⊆ Function.support (fun s => kernel s x) ∩ Icc ell R := by
    intro s hs
    exact ⟨Function.mem_support.mpr ((kernel_pos_iff (hell.trans hs.2.1.le)).mpr hs.1).ne',
      ⟨hs.2.1.le, hs.2.2.le⟩⟩
  apply (setIntegral_pos_iff_support_of_nonneg_ae ?_ (kernel_integrableOn hell)).2
  · exact hp.trans_le (measure_mono hsub)
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact kernel_nonneg (hell.trans hs.1)

private def logBody (t : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
  (Real.log x - Real.log d) *
    (g x - g (endpoint t)) / (weight t * t ^ (11 / 10 : ℝ))

private lemma crossing_label_small {t : ℝ} (ht : 256 ≤ t) {d : ℕ}
    (hd : (d : ℝ) ≤ endpoint t ^ (151 / 500 : ℝ)) : (d : ℝ) ≤ t / 4 := by
  have hB : 1 ≤ endpoint t := by
    have h : t ≤ endpoint t := le_add_of_nonneg_right
      (Real.rpow_nonneg (by linarith : 0 ≤ t) (4 / 5 : ℝ))
    linarith
  calc
    (d : ℝ) ≤ endpoint t ^ (151 / 500 : ℝ) := hd
    _ ≤ endpoint t ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hB (by norm_num)
    _ ≤ (2 * t) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by linarith) (endpoint_le_twice (by linarith)) (by norm_num)
    _ ≤ t / 4 := by
      rw [← Real.sqrt_eq_rpow]
      apply (Real.sqrt_le_iff).2
      constructor
      · positivity
      · nlinarith

private lemma logBody_antitone {t : ℝ} (ht : 256 ≤ t) {d : ℕ}
    (hd : 1 ≤ d) (hcut : (d : ℝ) ≤ endpoint t ^ (151 / 500 : ℝ)) :
    AntitoneOn (logBody t d) (Icc t (endpoint t)) := by
  have ht0 : 0 < t := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hden : 0 < weight t * t ^ (11 / 10 : ℝ) :=
    mul_pos (weight_pos (by linarith)) (Real.rpow_pos_of_pos ht0 _)
  have hsmall := crossing_label_small ht hcut
  have hD : ∀ x ∈ Icc t (endpoint t), HasDerivAt (logBody t d)
      ((1 / x * (g x - g (endpoint t)) - (Real.log x - Real.log d) * weight x) /
        (weight t * t ^ (11 / 10 : ℝ))) x := by
    intro x hx
    have hx1 : 1 < x := by linarith [hx.1]
    simpa only [logBody, activationDensity, weight, one_div, sub_eq_add_neg, mul_neg] using!
      (((Real.hasDerivAt_log (by linarith : x ≠ 0)).sub_const (Real.log d)).mul
        ((ActualRobinClockCovariance.g_has_deriv_at hx1).sub_const (g (endpoint t)))).div_const
          (weight t * t ^ (11 / 10 : ℝ))
  have hN : ∀ x ∈ Icc t (endpoint t),
      (1 / x * (g x - g (endpoint t)) - (Real.log x - Real.log d) * weight x) /
        (weight t * t ^ (11 / 10 : ℝ)) ≤ 0 := by
    intro x hx
    have hx0 : 0 < x := ht0.trans_le hx.1
    have hx1 : 1 < x := by linarith [hx.1]
    have hlx := Real.log_pos hx1
    have hlog : 1 ≤ Real.log x - Real.log d := by
      rw [← Real.log_div hx0.ne' hd0.ne']
      apply log_large
      exact (le_div_iff₀ hd0).2 (by linarith [hx.1])
    have hw := weight_pos hx1
    have hprice : 0 ≤ g (endpoint t) := by
      unfold g
      exact div_nonneg (by norm_num) (mul_nonneg (hx0.trans_le hx.2).le
        (Real.log_pos (show 1 < endpoint t by linarith [hx.2])).le)
    have hidentity : weight x = (1 / x) * g x + 1 / (x ^ 2 * Real.log x ^ 2) := by
      unfold weight g
      field_simp [hx0.ne', hlx.ne']
    have hder : (1 / x) * g x ≤ weight x := by
      rw [hidentity]
      exact le_add_of_nonneg_right (by positivity)
    apply div_nonpos_of_nonpos_of_nonneg _ hden.le
    nlinarith [mul_nonneg (by positivity : 0 ≤ 1 / x) hprice,
      mul_le_mul_of_nonneg_right hlog hw.le]
  exact antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
    (HasDerivAt.continuousOn hD)
    (fun x hx => (hD x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => hN x (interior_subset hx))

private lemma logBody_bounds {t : ℝ} (ht : 256 ≤ t) {d : ℕ}
    (hd : 1 ≤ d) (hcut : (d : ℝ) ≤ endpoint t ^ (151 / 500 : ℝ))
    {x : ℝ} (hx : x ∈ Icc t (endpoint t)) :
    0 ≤ logBody t d x ∧ logBody t d x ≤ lowerHeight t * Real.log (2 * t) := by
  have ht0 : 0 < t := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have htb : t ≤ endpoint t := le_add_of_nonneg_right (Real.rpow_nonneg ht0.le _)
  have ha := logBody_antitone ht hd hcut
  have hzero : logBody t d (endpoint t) = 0 := by simp [logBody]
  constructor
  · rw [← hzero]
    exact ha hx (right_mem_Icc.mpr htb) hx.2
  · have hlo := ha (left_mem_Icc.mpr htb) hx hx.1
    have hlogd : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
    have hlogt := Real.log_le_log ht0 (show t ≤ 2 * t by linarith)
    have hh := (height_bounds (show 4 ≤ t by linarith)).1
    have hbase : logBody t d t = lowerHeight t * (Real.log t - Real.log d) := by
      unfold logBody lowerHeight
      ring
    rw [hbase] at hlo
    exact hlo.trans (mul_le_mul_of_nonneg_left (by linarith) hh)

private def clampedLogBody (t : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
  logBody t d (max t (min x (endpoint t)))

private lemma clampedLogBody_antitone {t : ℝ} (ht : 256 ≤ t) {d : ℕ}
    (hd : 1 ≤ d) (hcut : (d : ℝ) ≤ endpoint t ^ (151 / 500 : ℝ)) :
    Antitone (clampedLogBody t d) := by
  have htb : t ≤ endpoint t := le_add_of_nonneg_right (Real.rpow_nonneg (by linarith) _)
  intro x y hxy
  apply logBody_antitone ht hd hcut
  · exact ⟨le_max_left _ _, max_le htb (min_le_right _ _)⟩
  · exact ⟨le_max_left _ _, max_le htb (min_le_right _ _)⟩
  · exact max_le_max_left _ (min_le_min_right _ hxy)

private lemma clampedLogBody_bounds {t : ℝ} (ht : 256 ≤ t) {d : ℕ}
    (hd : 1 ≤ d) (hcut : (d : ℝ) ≤ endpoint t ^ (151 / 500 : ℝ)) (x : ℝ) :
    0 ≤ clampedLogBody t d x ∧
      clampedLogBody t d x ≤ lowerHeight t * Real.log (2 * t) := by
  apply logBody_bounds ht hd hcut
  exact ⟨le_max_left _ _, max_le
    (le_add_of_nonneg_right (Real.rpow_nonneg (by linarith) _)) (min_le_right _ _)⟩

private lemma log_kernel_decomposition {t : ℝ} (ht : 256 ≤ t) {d : ℕ} (hd : 1 ≤ d)
    (x : ℝ) : Real.log (x / d) * kernel t x =
      clampedLogBody t d x - (if x ≤ t then logBody t d t else 0) := by
  have ht0 : 0 < t := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have htb : t ≤ endpoint t := le_add_of_nonneg_right (Real.rpow_nonneg ht0.le _)
  by_cases hxt : x ≤ t
  · rw [kernel_zero_of_outside (Or.inl hxt), if_pos hxt]
    simp [clampedLogBody, max_eq_left (le_trans (min_le_left _ _) hxt)]
  · rw [if_neg hxt]
    by_cases hxb : x ≤ endpoint t
    · rw [kernel, if_pos ⟨not_le.mp hxt, hxb⟩,
        Real.log_div (by linarith : x ≠ 0) hd0.ne']
      simp only [clampedLogBody, min_eq_left hxb, max_eq_right (not_le.mp hxt).le,
        logBody, sub_zero]
      ring
    · rw [kernel_zero_of_outside (Or.inr (not_le.mp hxb).le)]
      simp [clampedLogBody, min_eq_right (not_le.mp hxb).le, max_eq_right htb, logBody]


private lemma log_kernel_variation {t : ℝ} (ht : 256 ≤ t) {d : ℕ}
    (hd : 1 ≤ d) (hcut : (d : ℝ) ≤ endpoint t ^ (151 / 500 : ℝ)) :
    eVariationOn (fun x => Real.log (x / d) * kernel t x) univ ≤
      2 * ENNReal.ofReal (lowerHeight t * Real.log (2 * t)) := by
  let Q := lowerHeight t * Real.log (2 * t)
  let h := clampedLogBody t d
  let j : ℝ → ℝ := fun x => if x ≤ t then logBody t d t else 0
  have hjbounds : ∀ x, j x ∈ Icc 0 Q := by
    intro x
    have hb := logBody_bounds ht hd hcut (x := t)
      (left_mem_Icc.mpr (le_add_of_nonneg_right (Real.rpow_nonneg (by linarith) _)))
    dsimp [j]
    split_ifs
    · exact hb
    · exact ⟨le_rfl, (clampedLogBody_bounds ht hd hcut t).1.trans
        (clampedLogBody_bounds ht hd hcut t).2⟩
  have hjanti : Antitone j := by
    intro x y hxy
    dsimp [j]
    split_ifs <;> grind [hjbounds t]
  have hhvar : eVariationOn h univ ≤ ENNReal.ofReal Q := by
    have hbound := eVariationOn.comp_le_of_antitoneOn id (s := Icc 0 Q) h
      ((clampedLogBody_antitone ht hd hcut).antitoneOn univ)
      (fun x _ => clampedLogBody_bounds ht hd hcut x)
    simpa only [Function.id_comp, eVariationOn_id_Icc, sub_zero] using hbound
  have hjvar : eVariationOn j univ ≤ ENNReal.ofReal Q := by
    have hbound := eVariationOn.comp_le_of_antitoneOn id (s := Icc 0 Q) j (hjanti.antitoneOn univ)
      (fun x _ => hjbounds x)
    simpa only [Function.id_comp, eVariationOn_id_Icc, sub_zero] using hbound
  have heq : (fun x => Real.log (x / d) * kernel t x) = fun x => h x - j x := by
    funext x
    exact log_kernel_decomposition ht hd x
  rw [heq, eVariationOn]
  apply iSup_le
  rintro ⟨n, ⟨u, hu, hus⟩⟩
  calc
    _ ≤ (∑ i ∈ Finset.range n, edist (h (u (i + 1))) (h (u i))) +
        ∑ i ∈ Finset.range n, edist (j (u (i + 1))) (j (u i)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      simpa only [sub_eq_add_neg, edist_neg_neg] using
        edist_add_add_le (h (u (i + 1))) (-j (u (i + 1))) (h (u i)) (-j (u i))
    _ ≤ ENNReal.ofReal Q + ENNReal.ofReal Q := add_le_add
      ((eVariationOn.sum_le hu hus).trans hhvar) ((eVariationOn.sum_le hu hus).trans hjvar)
    _ = _ := by rw [two_mul]

private def localRatio (ell R t : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
  if x ≤ t then 1 else if endpoint t ≤ x then 0 else beforeRatio ell R d x

private lemma localRatio_bounds {ell R t : ℝ} (hell : 256 ≤ ell) (horder : ell < R)
    (ht : t ∈ Icc ell R) (d : ℕ) (x : ℝ) : localRatio ell R t d x ∈ Icc 0 1 := by
  unfold localRatio
  split_ifs with hx hB
  · norm_num
  · norm_num
  · have hk : 0 < kernel t x := (kernel_pos_iff (by linarith [ht.1])).mpr
      ⟨not_le.mp hx, not_le.mp hB⟩
    exact beforeRatio_bounds (by linarith) d (windowMass_pos_of_kernel_pos (by linarith)
      horder ht hk)

private lemma localRatio_antitone {ell R t : ℝ} (hell : 256 ≤ ell) (horder : ell < R)
    (ht : t ∈ Icc ell R) (d : ℕ) : Antitone (localRatio ell R t d) := by
  intro x y hxy
  by_cases hx : x ≤ t
  · simpa [localRatio, hx] using (localRatio_bounds hell horder ht d y).2
  by_cases hy : endpoint t ≤ y
  · simpa [localRatio, hy, show ¬y ≤ t by
      have hw : 0 < width t := Real.rpow_pos_of_pos (by linarith [ht.1]) _
      dsimp [endpoint] at hy
      linarith] using (localRatio_bounds hell horder ht d x).1
  have hyL : ¬y ≤ t := not_le.mpr ((not_le.mp hx).trans_le hxy)
  have hxR : ¬endpoint t ≤ x := not_le.mpr (hxy.trans_lt (not_le.mp hy))
  simp only [localRatio, if_neg hx, if_neg hyL, if_neg hxR, if_neg hy]
  have hKx := windowMass_pos_of_kernel_pos (by linarith : 4 ≤ ell) horder ht
    ((kernel_pos_iff (by linarith [ht.1] : 4 ≤ t)).mpr ⟨not_le.mp hx, not_le.mp hxR⟩)
  have hKy := windowMass_pos_of_kernel_pos (by linarith : 4 ≤ ell) horder ht
    ((kernel_pos_iff (by linarith [ht.1] : 4 ≤ t)).mpr ⟨not_le.mp hyL, not_le.mp hy⟩)
  exact beforeRatio_antitoneOn_positive (by linarith) d (by linarith [ht.1, not_le.mp hx])
    hxy hKx hKy

private lemma cutRow_eq_local {ell R t : ℝ} (d : ℕ) (x : ℝ) :
    cutRow ell R t d x = Real.log (x / d) * kernel t x *
      ((if t < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0) - localRatio ell R t d x) := by
  unfold cutRow localRatio
  by_cases hx : x ≤ t
  · simp [hx, kernel_zero_of_outside (Or.inl hx)]
  by_cases hB : endpoint t ≤ x
  · simp [hB, hx, kernel_zero_of_outside (Or.inr hB)]
  · simp [hx, hB]

private lemma cutRow_single_variation {ell R t : ℝ} (hell : 256 ≤ ell) (horder : ell < R)
    (ht : t ∈ Icc ell R) {d : ℕ} (hd : 1 ≤ d)
    (hcut : (d : ℝ) ≤ endpoint t ^ (151 / 500 : ℝ)) :
    eVariationOn (cutRow ell R t d) univ ≤
      ENNReal.ofReal (3 * lowerHeight t * Real.log (2 * t)) := by
  let q : ℝ → ℝ := fun x => Real.log (x / d) * kernel t x
  let c : ℝ := if t < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0
  let r := localRatio ell R t d
  let Q : ℝ := lowerHeight t * Real.log (2 * t)
  have ht256 : 256 ≤ t := hell.trans ht.1
  have hQ : 0 ≤ Q := mul_nonneg (height_bounds (by linarith : 4 ≤ t)).1
    (Real.log_nonneg (by linarith))
  have hq : ∀ x ∈ univ, ‖q x‖ₑ ≤ ENNReal.ofReal Q := by
    intro x _
    rw [Real.enorm_eq_ofReal_abs]
    apply ENNReal.ofReal_le_ofReal
    change |Real.log (x / d) * kernel t x| ≤ Q
    have hb := clampedLogBody_bounds ht256 hd hcut x
    by_cases hx : x ≤ t
    · have hz := kernel_zero_of_outside (t := t) (Or.inl hx)
      change |Real.log (x / d) * kernel t x| ≤ Q
      simp only [hz, mul_zero, abs_zero]
      exact hQ
    · rw [log_kernel_decomposition ht256 hd]
      simpa only [if_neg hx, sub_zero, abs_of_nonneg hb.1] using hb.2
  have hr : ∀ x ∈ univ, ‖c - r x‖ₑ ≤ (1 : ℝ≥0∞) := by
    intro x _
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have hb := localRatio_bounds hell horder ht d x
    change 0 ≤ localRatio ell R t d x ∧ localRatio ell R t d x ≤ 1 at hb
    dsimp [c, r]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  have hrvar : eVariationOn r univ ≤ (1 : ℝ≥0∞) := by
    have hv := eVariationOn.comp_le_of_antitoneOn id (s := Icc 0 1) r
      ((localRatio_antitone hell horder ht d).antitoneOn univ)
      (fun x _ => localRatio_bounds hell horder ht d x)
    simpa only [Function.id_comp, eVariationOn_id_Icc, sub_zero, ENNReal.ofReal_one] using hv
  have hcvar : eVariationOn (fun x => c - r x) univ = eVariationOn r univ := by
    unfold eVariationOn
    congr 1
    funext p
    apply Finset.sum_congr rfl
    intro i _
    rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq,
      show (c - r (p.2.1 (i + 1))) - (c - r (p.2.1 i)) =
        r (p.2.1 i) - r (p.2.1 (i + 1)) by ring, abs_sub_comm]
  have hprod := eVariation_mul_le hq hr
  have hrow : cutRow ell R t d = q * (fun x => c - r x) := by
    funext x
    exact cutRow_eq_local d x
  rw [hrow]
  apply hprod.trans
  rw [hcvar]
  calc
    _ ≤ ENNReal.ofReal Q * 1 + 1 * (2 * ENNReal.ofReal Q) :=
      by
        gcongr <;> exact log_kernel_variation ht256 hd hcut
    _ = ENNReal.ofReal (3 * lowerHeight t * Real.log (2 * t)) := by
      rw [mul_one, one_mul, show ENNReal.ofReal Q + 2 * ENNReal.ofReal Q =
        3 * ENNReal.ofReal Q by ring, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      dsimp [Q]
      ring

private lemma boundedVariation_intervalIntegrable {f : ℝ → ℝ}
    (hf : BoundedVariationOn f univ) (a b : ℝ) : IntervalIntegrable f volume a b := by
  obtain ⟨p, q, hp, hq, heq⟩ := hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  rw [monotoneOn_univ] at hp hq
  rw [heq]
  exact hp.intervalIntegrable.sub hq.intervalIntegrable

private lemma lattice_cell_error {f : ℝ → ℝ} (hf : BoundedVariationOn f univ)
    {d : ℝ} (hd : 0 < d) (i : ℕ) :
    |d * f (d * i) - ∫ x in d * i..d * (i + 1), f x| ≤
      d * (eVariationOn f (Icc (d * i) (d * (i + 1)))).toReal := by
  have hi := boundedVariation_intervalIntegrable hf (d * i) (d * (i + 1))
  have hab : d * i ≤ d * (i + 1) := by nlinarith
  let V := (eVariationOn f (Icc (d * i) (d * (i + 1)))).toReal
  have hbd : ∀ x ∈ Icc (d * i) (d * (i + 1)), |f (d * i) - f x| ≤ V := by
    intro x hx
    exact (Real.dist_eq _ _).symm ▸
      (hf.mono (subset_univ _)).dist_le
        (left_mem_Icc.mpr hab) hx
  calc
    _ = |∫ x in d * i..d * (i + 1), f (d * i) - f x| := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hi, intervalIntegral.integral_const]
      congr 1
      simp only [smul_eq_mul]
      ring
    _ ≤ ∫ x in d * i..d * (i + 1), |f (d * i) - f x| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ _x in d * i..d * (i + 1), V :=
      intervalIntegral.integral_mono_on hab (intervalIntegrable_const.sub hi).abs
        intervalIntegrable_const hbd
    _ = _ := by simp only [intervalIntegral.integral_const, smul_eq_mul]; dsimp [V]; ring

private lemma lattice_error_variation {f : ℝ → ℝ} (hf : BoundedVariationOn f univ)
    {d : ℝ} (hd : 0 < d) (N : ℕ) :
    |(∑ i ∈ Finset.range N, f (d * i)) - (∫ x in 0..d * N, f x) / d| ≤
      (eVariationOn f univ).toReal := by
  have hstep : Monotone (fun i : ℕ => d * i) := by
    intro i j hij
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hij) hd.le
  have hsum := eVariationOn.sum' f hstep (n := N)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero] at hsum
  have hfinite : ∀ i ∈ Finset.range N,
      eVariationOn f (Icc (d * i) (d * (i + 1))) ≠ ⊤ :=
    fun i _ => hf.mono (subset_univ _)
  have hsumreal : (∑ i ∈ Finset.range N,
      (eVariationOn f (Icc (d * i) (d * (i + 1)))).toReal) ≤
      (eVariationOn f univ).toReal := by
    rw [← ENNReal.toReal_sum hfinite, hsum]
    exact ENNReal.toReal_mono hf (eVariationOn.mono _ (subset_univ _))
  have hpieces : (∑ i ∈ Finset.range N, ∫ x in d * i..d * (i + 1), f x) =
      ∫ x in 0..d * N, f x := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero] using
      intervalIntegral.sum_integral_adjacent_intervals (a := fun i : ℕ => d * (i : ℝ)) (n := N)
      (fun i (_hi : i < N) => by
        simpa only [Nat.cast_add, Nat.cast_one] using
          boundedVariation_intervalIntegrable hf (d * i) (d * (i + 1)))
  have htotal : |d * (∑ i ∈ Finset.range N, f (d * i)) - ∫ x in 0..d * N, f x| ≤
      d * (eVariationOn f univ).toReal := by
    rw [← hpieces, Finset.mul_sum, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i ∈ Finset.range N, |d * f (d * i) - ∫ x in d * i..d * (i + 1), f x| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range N,
          d * (eVariationOn f (Icc (d * i) (d * (i + 1)))).toReal :=
        Finset.sum_le_sum (fun i _ => lattice_cell_error hf hd i)
      _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hsumreal hd.le
  have heq : |d * (∑ i ∈ Finset.range N, f (d * i)) - ∫ x in 0..d * N, f x| =
      d * |(∑ i ∈ Finset.range N, f (d * i)) - (∫ x in 0..d * N, f x) / d| := by
    calc
      _ = |d * ((∑ i ∈ Finset.range N, f (d * i)) -
          (∫ x in 0..d * N, f x) / d)| := by
        congr 1
        field_simp
      _ = _ := by rw [abs_mul, abs_of_pos hd]
  rw [heq] at htotal
  exact (mul_le_mul_iff_right₀ hd).mp htotal

/-- The complete positive cofactor row with its signed continuum compensation. -/
def latticeRowRemainder (ell R t : ℝ) (d : ℕ) : ℝ :=
  (∑ m ∈ Finset.Icc 1 (⌊2 * R⌋₊ / d),
    Real.log (m : ℝ) * kernel t ((d : ℝ) * m) *
      ((if t < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0) -
        beforeRatio ell R d ((d : ℝ) * m))) -
      (∫ x in t..endpoint t, cutRow ell R t d x) / d

private lemma cutRow_zero_of_outside {ell R t x : ℝ} (d : ℕ)
    (hx : x ≤ t ∨ endpoint t ≤ x) : cutRow ell R t d x = 0 := by
  simp only [cutRow, kernel_zero_of_outside hx, mul_zero, zero_mul]

private lemma cutRow_integral_full_grid {ell R t L : ℝ} {d : ℕ}
    (ht0 : 0 ≤ t) (hL : endpoint t ≤ L)
    (hf : BoundedVariationOn (cutRow ell R t d) univ) :
    (∫ x in 0..L, cutRow ell R t d x) = ∫ x in t..endpoint t, cutRow ell R t d x := by
  have hleft : (∫ x in 0..t, cutRow ell R t d x) = 0 := by
    rw [intervalIntegral.integral_of_le ht0]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    exact cutRow_zero_of_outside d (Or.inl hx.2)
  have hright : (∫ x in endpoint t..L, cutRow ell R t d x) = 0 := by
    rw [intervalIntegral.integral_of_le hL]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    exact cutRow_zero_of_outside d (Or.inr hx.1.le)
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (boundedVariation_intervalIntegrable hf 0 t) (boundedVariation_intervalIntegrable hf t L),
    ← intervalIntegral.integral_add_adjacent_intervals
      (boundedVariation_intervalIntegrable hf t (endpoint t))
      (boundedVariation_intervalIntegrable hf (endpoint t) L), hleft, hright]
  simp


private lemma cutRow_zero_above {ell R t : ℝ} (hell : 256 ≤ ell) (horder : ell < R)
    (ht : t ∈ Icc ell R) {d : ℕ}
    (hd : endpoint t ^ (151 / 500 : ℝ) ≤ (d : ℝ)) (x : ℝ) :
    cutRow ell R t d x = 0 := by
  have ht4 : 4 ≤ t := by linarith [ht.1]
  have ht0 : 0 < t := by linarith [ht.1]
  have hB : 0 < endpoint t := ht0.trans_le
    (le_add_of_nonneg_right (Real.rpow_nonneg ht0.le _))
  have hclock : endpoint t ≤ (d : ℝ) ^ (500 / 151 : ℝ) := by
    calc
      endpoint t = (endpoint t ^ (151 / 500 : ℝ)) ^ (500 / 151 : ℝ) := by
        rw [← Real.rpow_mul hB.le]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hB.le _) hd (by norm_num)
  by_cases hz : kernel t x = 0
  · simp [cutRow, hz]
  have hk : 0 < kernel t x := lt_of_le_of_ne (kernel_nonneg ht4) (Ne.symm hz)
  have hx := (kernel_pos_iff ht4).mp hk
  have hK := windowMass_pos_of_kernel_pos (by linarith : 4 ≤ ell) horder ht hk
  have hlate : afterMass ell R d x = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro s hs
    exact kernel_zero_of_outside (Or.inl
      (hx.2.le.trans (hclock.trans (not_lt.mp hs.2))))
  have hratio : beforeRatio ell R d x = 1 := by
    have hN : beforeMass ell R d x = windowMass ell R x := by
      linarith [mass_split (by linarith : 4 ≤ ell) d (R := R) (x := x)]
    unfold beforeRatio
    rw [hN, div_self hK.ne']
  have hactive : t < (d : ℝ) ^ (500 / 151 : ℝ) :=
    (lt_add_of_pos_right t (Real.rpow_pos_of_pos ht0 (4 / 5 : ℝ))).trans_le hclock
  simp [cutRow, hratio, hactive]

/- The lower crossing clock is used only as a support cutoff.  It is deliberately
   defined by the explicit inequality `u+u^(4/5)≤t`; no inverse selection is
   introduced into the original family. -/
private def lowerClock (t : ℝ) : ℝ := t - width t

private lemma width_le_third {t : ℝ} (ht : 256 ≤ t) : width t ≤ t / 3 := by
  have ht0 : 0 < t := by linarith
  have ht243 : (243 : ℝ) ≤ t := by linarith
  have hpow := Real.rpow_le_rpow (show 0 ≤ (243 : ℝ) by norm_num) ht243
    (show 0 ≤ (1 / 5 : ℝ) by norm_num)
  have hthree : (3 : ℝ) ≤ t ^ (1 / 5 : ℝ) := by
    convert hpow using 1
    · rw [show (243 : ℝ) = 3 ^ (5 : ℕ) by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
  have hdecomp : t = t ^ (4 / 5 : ℝ) * t ^ (1 / 5 : ℝ) := by
    rw [← Real.rpow_add ht0]
    norm_num
  unfold width
  have hmul := mul_le_mul_of_nonneg_left hthree
    (Real.rpow_nonneg ht0.le (4 / 5 : ℝ))
  rw [← hdecomp] at hmul
  nlinarith

private lemma lowerClock_bounds {t : ℝ} (ht : 256 ≤ t) :
    0 < lowerClock t ∧ 2 * t / 3 ≤ lowerClock t ∧ lowerClock t ≤ t := by
  have ht0 : 0 < t := by linarith
  have hw := width_le_third ht
  have hwn : 0 ≤ width t := by
    unfold width
    positivity
  unfold lowerClock
  constructor
  · linarith
  constructor
  · linarith
  · linarith

private lemma lowerClock_endpoint_le {t : ℝ} (ht : 256 ≤ t) :
    endpoint (lowerClock t) ≤ t := by
  have hu := lowerClock_bounds ht
  have hw := width_le_third ht
  have hpow : width (lowerClock t) ≤ width t := by
    unfold width
    exact Real.rpow_le_rpow hu.1.le hu.2.2 (by norm_num)
  unfold endpoint
  dsimp [lowerClock] at *
  linarith

private lemma lowerClock_rpow_cutoff {t : ℝ} (ht : 256 ≤ t) {d : ℕ}
    (hd : 1 ≤ d) (hcut : (d : ℝ) ≤ lowerClock t ^ (151 / 500 : ℝ)) :
    (d : ℝ) ^ (500 / 151 : ℝ) ≤ lowerClock t := by
  have hu := lowerClock_bounds ht
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hpow := Real.rpow_le_rpow (show 0 ≤ (d : ℝ) by linarith)
    hcut (show 0 ≤ (500 / 151 : ℝ) by norm_num)
  have hright : (lowerClock t ^ (151 / 500 : ℝ)) ^ (500 / 151 : ℝ) = lowerClock t := by
    rw [← Real.rpow_mul hu.1.le]
    norm_num
  rw [hright] at hpow
  exact hpow

private lemma cutRow_zero_below {ell R t : ℝ} (hell : 256 ≤ ell) (horder : ell < R)
    (ht : t ∈ Icc ell R) {d : ℕ} (hd : 1 ≤ d)
    (hcut : (d : ℝ) ≤ lowerClock t ^ (151 / 500 : ℝ)) (x : ℝ) :
    cutRow ell R t d x = 0 := by
  have ht4 : 4 ≤ t := by linarith [hell, ht.1]
  have ht0 : 0 < t := by linarith [ht.1]
  have hτ := lowerClock_rpow_cutoff (hell.trans ht.1) hd hcut
  have hu := lowerClock_bounds (hell.trans ht.1)
  have hclock : endpoint ((d : ℝ) ^ (500 / 151 : ℝ)) ≤ t := by
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hτ1 : (1 : ℝ) ≤ (d : ℝ) ^ (500 / 151 : ℝ) :=
      Real.one_le_rpow hd1 (by norm_num)
    have hu1 : (1 : ℝ) ≤ lowerClock t := by linarith [hu.2.1]
    exact (endpoint_strictMonoOn.monotoneOn hτ1 hu1 hτ).trans
      (lowerClock_endpoint_le (hell.trans ht.1))
  by_cases hz : kernel t x = 0
  · simp [cutRow, hz]
  have hk : 0 < kernel t x := lt_of_le_of_ne (kernel_nonneg ht4) (Ne.symm hz)
  have hx := (kernel_pos_iff ht4).mp hk
  have hlate : beforeMass ell R d x = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro s hs
    apply kernel_zero_of_outside
    right
    have hsτ : s < (d : ℝ) ^ (500 / 151 : ℝ) := hs.2
    have hs1 : (1 : ℝ) ≤ s := by linarith [hell, hs.1.1]
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hτ1 : (1 : ℝ) ≤ (d : ℝ) ^ (500 / 151 : ℝ) :=
      Real.one_le_rpow hd1 (by norm_num)
    have hse : endpoint s ≤ endpoint ((d : ℝ) ^ (500 / 151 : ℝ)) :=
      endpoint_strictMonoOn.monotoneOn hs1 hτ1 (le_of_lt hsτ)
    exact (hse.trans_lt (hclock.trans_lt hx.1)).le
  have hratio : beforeRatio ell R d x = 0 := by
    unfold beforeRatio
    rw [hlate, zero_div]
  have hactive : ¬ t < (d : ℝ) ^ (500 / 151 : ℝ) := by
    exact not_lt_of_ge (hτ.trans hu.2.2)
  simp [cutRow, hratio, hactive]

private lemma crossing_width_bound {t : ℝ} (ht : 256 ≤ t) :
    endpoint t ^ (151 / 500 : ℝ) - lowerClock t ^ (151 / 500 : ℝ) ≤
      (151 / 125 : ℝ) * t ^ (51 / 500 : ℝ) := by
  let a : ℝ := 151 / 500
  have ht0 : 0 < t := by linarith
  have hu := lowerClock_bounds ht
  have hlow0 : 0 < lowerClock t := hu.1
  have hB0 : 0 < endpoint t := by
    dsimp [endpoint, width]
    positivity
  have hdelta : 0 ≤ endpoint t - lowerClock t := by
    dsimp [endpoint, lowerClock, width]
    ring_nf
    positivity
  have hq : 0 ≤ (endpoint t - lowerClock t) / lowerClock t :=
    div_nonneg hdelta hlow0.le
  have hrepr : endpoint t = lowerClock t *
      (1 + (endpoint t - lowerClock t) / lowerClock t) := by
    field_simp [hlow0.ne']
    ring
  have hbern := rpow_one_add_le_one_add_mul_self (s :=
      (endpoint t - lowerClock t) / lowerClock t) (by linarith) (by norm_num : 0 ≤ a)
      (by norm_num : a ≤ 1)
  have hBpow : endpoint t ^ a = lowerClock t ^ a *
      (1 + (endpoint t - lowerClock t) / lowerClock t) ^ a := by
    calc
      _ = (lowerClock t *
          (1 + (endpoint t - lowerClock t) / lowerClock t)) ^ a :=
        congrArg (fun z : ℝ => z ^ a) hrepr
      _ = _ := by rw [Real.mul_rpow hlow0.le (by positivity)]
  have hstep : endpoint t ^ a - lowerClock t ^ a ≤
      a * lowerClock t ^ (a - 1) * (endpoint t - lowerClock t) := by
    have hnonneg : 0 ≤ lowerClock t ^ a := Real.rpow_nonneg hlow0.le _
    have hmain : endpoint t ^ a - lowerClock t ^ a ≤
        lowerClock t ^ a * (a *
          ((endpoint t - lowerClock t) / lowerClock t)) := by
      rw [hBpow]
      nlinarith
    calc
      _ ≤ _ := hmain
      _ = _ := by
        rw [Real.rpow_sub hlow0]
        field_simp [hlow0.ne']
        simp only [Real.rpow_one]
        ring
  have hfac : lowerClock t ^ (a - 1) ≤ 2 * t ^ (a - 1) := by
    have hbase : (2 * t / 3 : ℝ) ≤ lowerClock t := hu.2.1
    have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ 2 * t / 3) hbase
      (by norm_num : 0 ≤ 1 - a)
    have hneg : lowerClock t ^ (a - 1) ≤ (2 * t / 3) ^ (a - 1) := by
      have hlneg : lowerClock t ^ (a - 1) =
          1 / lowerClock t ^ (1 - a) := by
        rw [show a - 1 = -(1 - a) by ring]
        simpa only [one_div] using
          (Real.rpow_neg (show 0 ≤ lowerClock t by linarith) (1 - a))
      have htneg : (2 * t / 3) ^ (a - 1) =
          1 / (2 * t / 3) ^ (1 - a) := by
        rw [show a - 1 = -(1 - a) by ring]
        simpa only [one_div] using
          (Real.rpow_neg (show 0 ≤ 2 * t / 3 by positivity) (1 - a))
      rw [hlneg, htneg]
      exact one_div_le_one_div_of_le (by positivity) hpow
    have hconst : (2 / 3 : ℝ) ^ (a - 1) ≤ 2 := by
      rw [show a - 1 = -(1 - a) by ring, Real.rpow_neg (by norm_num)]
      have hsmall := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 2 / 3)
        (by norm_num : (2 / 3 : ℝ) ≤ 1) (by norm_num : 1 - a ≤ 1)
      have hqpos : 0 < (2 / 3 : ℝ) ^ (1 - a) := Real.rpow_pos_of_pos (by norm_num) _
      have hsmall' : (2 / 3 : ℝ) ≤ (2 / 3 : ℝ) ^ (1 - a) := by
        simpa only [Real.rpow_one] using hsmall
      have hrec := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2 / 3) hsmall'
      have hrec' : 1 / ((2 / 3 : ℝ) ^ (1 - a)) ≤ 2 := by
        calc
          _ ≤ 1 / (2 / 3 : ℝ) := hrec
          _ ≤ 2 := by norm_num
      simpa [one_div] using hrec'
    calc
      _ ≤ (2 * t / 3) ^ (a - 1) := hneg
      _ = (2 / 3 : ℝ) ^ (a - 1) * t ^ (a - 1) := by
        rw [show 2 * t / 3 = (2 / 3 : ℝ) * t by ring,
          Real.mul_rpow (by norm_num) ht0.le]
      _ ≤ 2 * t ^ (a - 1) := by
        gcongr
  have hdelta_le : endpoint t - lowerClock t ≤ 2 * t ^ (4 / 5 : ℝ) := by
    dsimp [endpoint, lowerClock, width]
    nlinarith
  have hpowadd : t ^ (a - 1) * t ^ (4 / 5 : ℝ) = t ^ (51 / 500 : ℝ) := by
    rw [← Real.rpow_add ht0]
    norm_num [a]
  have hprod := mul_le_mul hfac hdelta_le (by positivity) (by positivity)
  have hmain_bound : a * lowerClock t ^ (a - 1) * (endpoint t - lowerClock t) ≤
      a * (2 * t ^ (a - 1)) * (2 * t ^ (4 / 5 : ℝ)) := by
    calc
      _ = a * (lowerClock t ^ (a - 1) * (endpoint t - lowerClock t)) := by ring
      _ ≤ a * ((2 * t ^ (a - 1)) * (2 * t ^ (4 / 5 : ℝ))) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = _ := by ring
  have hmain := hstep.trans hmain_bound
  calc
    _ ≤ a * (2 * t ^ (a - 1)) * (2 * t ^ (4 / 5 : ℝ)) := hmain
    _ = (4 * a) * t ^ (a - 1) * t ^ (4 / 5 : ℝ) := by ring
    _ = (4 * a) * (t ^ (a - 1) * t ^ (4 / 5 : ℝ)) := by ring
    _ = (151 / 125 : ℝ) * t ^ (51 / 500 : ℝ) := by
      rw [hpowadd]
      norm_num [a]

private lemma crossing_count {t : ℝ} (ht : 256 ≤ t) :
    ((Finset.Icc (⌊lowerClock t ^ (151 / 500 : ℝ)⌋₊ + 1)
      (⌊endpoint t ^ (151 / 500 : ℝ)⌋₊)).card : ℝ) ≤ 2 * t ^ (51 / 500 : ℝ) := by
  let a : ℝ := 151 / 500
  have hu := lowerClock_bounds ht
  have hlow : 0 ≤ lowerClock t ^ a := Real.rpow_nonneg hu.1.le _
  have hupper : 0 ≤ endpoint t ^ a := by
    have : 0 ≤ endpoint t := by
      dsimp [endpoint, width]
      positivity
    exact Real.rpow_nonneg this _
  have horder : lowerClock t ^ a ≤ endpoint t ^ a := by
    have hbase : 0 ≤ lowerClock t := hu.1.le
    have hle : lowerClock t ≤ endpoint t := by
      dsimp [endpoint, width]
      linarith [Real.rpow_nonneg (by linarith [hu.2.2] : 0 ≤ t) (4 / 5 : ℝ)]
    exact Real.rpow_le_rpow hbase hle (by norm_num)
  have hfloor : ⌊lowerClock t ^ a⌋₊ ≤ ⌊endpoint t ^ a⌋₊ :=
    Nat.le_floor ((Nat.floor_le hlow).trans horder)
  have hcard := Nat.card_Icc (⌊lowerClock t ^ a⌋₊ + 1)
    (⌊endpoint t ^ a⌋₊)
  have hcast : ((Finset.Icc (⌊lowerClock t ^ a⌋₊ + 1)
      (⌊endpoint t ^ a⌋₊)).card : ℝ) =
      (⌊endpoint t ^ a⌋₊ : ℝ) - (⌊lowerClock t ^ a⌋₊ : ℝ) := by
    rw [hcard]
    have hnat : ⌊endpoint t ^ a⌋₊ + 1 - (⌊lowerClock t ^ a⌋₊ + 1) =
        ⌊endpoint t ^ a⌋₊ - ⌊lowerClock t ^ a⌋₊ := by omega
    rw [hnat, Nat.cast_sub hfloor]
  have hupper_floor : (⌊endpoint t ^ a⌋₊ : ℝ) ≤ endpoint t ^ a := Nat.floor_le hupper
  have hlower_floor : lowerClock t ^ a - 1 < (⌊lowerClock t ^ a⌋₊ : ℝ) := by
    have h := (Nat.floor_lt hlow (n := ⌊lowerClock t ^ a⌋₊ + 1)).mp
      (by omega : ⌊lowerClock t ^ a⌋₊ < ⌊lowerClock t ^ a⌋₊ + 1)
    norm_num at h ⊢
    linarith
  rw [hcast]
  have hw := crossing_width_bound ht
  have hpow1 : (1 : ℝ) ≤ t ^ (51 / 500 : ℝ) := by
    exact Real.one_le_rpow (by linarith) (by norm_num)
  have hpow15 : (3 / 2 : ℝ) ≤ t ^ (51 / 500 : ℝ) := by
    have ht243 : (243 : ℝ) ≤ t := by linarith
    have hfive := Real.rpow_le_rpow (show 0 ≤ (243 : ℝ) by norm_num) ht243
      (show 0 ≤ (1 / 5 : ℝ) by norm_num)
    have hthree : (3 : ℝ) ≤ t ^ (1 / 5 : ℝ) := by
      convert hfive using 1
      · rw [show (243 : ℝ) = 3 ^ (5 : ℕ) by norm_num, ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
        norm_num
    have hten : (3 / 2 : ℝ) ≤ t ^ (1 / 10 : ℝ) := by
      have hsq : (t ^ (1 / 10 : ℝ)) ^ (2 : ℕ) = t ^ (1 / 5 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ t)]
        norm_num
      have hpos : 0 ≤ t ^ (1 / 10 : ℝ) := Real.rpow_nonneg (by linarith) _
      nlinarith [hsq]
    exact hten.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
  have hw' : endpoint t ^ a - lowerClock t ^ a ≤
      (151 / 125 : ℝ) * t ^ (51 / 500 : ℝ) := by
    simpa [a] using hw
  nlinarith [hw', hpow15]

/-- The actual moving-cut row pays every lattice cell, including both terminal cells. -/
theorem original_cut_row_lattice_estimate {ell R t : ℝ}
    (hell : 256 ≤ ell) (horder : ell < R) (ht : t ∈ Icc ell R) {d : ℕ}
    (hd : 1 ≤ d) :
    |latticeRowRemainder ell R t d| ≤ 3 * lowerHeight t * Real.log (2 * t) := by
  by_cases hcut : (d : ℝ) ≤ endpoint t ^ (151 / 500 : ℝ)
  ·
    have ht256 := hell.trans ht.1
    have ht0 : 0 < t := by linarith
    have hd0 : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd
    have hdreal : (0 : ℝ) < d := by exact_mod_cast hd0
    have hV := cutRow_single_variation hell horder ht hd hcut
    have hf : BoundedVariationOn (cutRow ell R t d) univ := (hV.trans_lt ENNReal.ofReal_lt_top).ne
    let N : ℕ := ⌊2 * R⌋₊
    have hnat : N + 1 ≤ d * (N / d + 1) := by
      have hr := Nat.mod_lt N hd0
      have he := Nat.div_add_mod N d
      nlinarith
    have hL : endpoint t ≤ (d : ℝ) * ((N / d + 1 : ℕ) : ℝ) := by
      have hcast : (N : ℝ) + 1 ≤ (d : ℝ) * ((N / d + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
      have hfloor : 2 * R < (N : ℝ) + 1 := Nat.lt_floor_add_one (2 * R)
      exact (endpoint_le_twice (by linarith)).trans
        ((mul_le_mul_of_nonneg_left ht.2 (by norm_num)).trans (hfloor.le.trans hcast))
    have hgrid := lattice_error_variation hf hdreal (N / d + 1)
    have hint := cutRow_integral_full_grid ht0.le hL hf
    rw [hint] at hgrid
    have hset : Finset.range (N / d + 1) = insert 0 (Finset.Icc 1 (N / d)) := by
      rw [Nat.range_succ_eq_Icc_zero]
      simpa using (Finset.insert_Icc_succ_left_eq_Icc (a := 0) (b := N / d)
        (Nat.zero_le _)).symm
    rw [hset, Finset.sum_insert (by simp)] at hgrid
    simp only [Nat.cast_zero, mul_zero, cutRow_zero_of_outside d (Or.inl ht0.le), zero_add] at hgrid
    have hrow : (∑ m ∈ Finset.Icc 1 (N / d), cutRow ell R t d ((d : ℝ) * m)) =
        ∑ m ∈ Finset.Icc 1 (N / d), Real.log (m : ℝ) * kernel t ((d : ℝ) * m) *
          ((if t < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0) -
            beforeRatio ell R d ((d : ℝ) * m)) := by
      apply Finset.sum_congr rfl
      intro m _
      unfold cutRow
      rw [mul_div_cancel_left₀ (m : ℝ) hdreal.ne']
    rw [hrow] at hgrid
    exact hgrid.trans (ENNReal.toReal_le_of_le_ofReal
      (mul_nonneg (mul_nonneg (by norm_num)
        (height_bounds (by linarith [ht.1] : 4 ≤ t)).1)
        (Real.log_nonneg (by linarith [ht.1]))) hV)
  · have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
    have hz : cutRow ell R t d = fun _ => 0 := by
      funext x
      exact cutRow_zero_above hell horder ht (not_le.mp hcut).le x
    have hsum : (∑ m ∈ Finset.Icc 1 (⌊2 * R⌋₊ / d),
        Real.log (m : ℝ) * kernel t ((d : ℝ) * m) *
          ((if t < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0) -
            beforeRatio ell R d ((d : ℝ) * m))) = 0 := by
      apply Finset.sum_eq_zero
      intro m _
      have h := congrFun hz ((d : ℝ) * m)
      simpa only [cutRow, mul_div_cancel_left₀ (m : ℝ) hd0.ne'] using h
    unfold latticeRowRemainder
    rw [hsum, hz]
    simp only [intervalIntegral.integral_zero, zero_div, sub_zero, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (height_bounds (by linarith [ht.1] : 4 ≤ t)).1)
      (Real.log_nonneg (by linarith [ht.1]))

private lemma latticeRowRemainder_zero_of_cutRow {ell R t : ℝ} {d : ℕ}
    (hd : 1 ≤ d) (hzero : cutRow ell R t d = fun _ => 0) :
    latticeRowRemainder ell R t d = 0 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hsum : (∑ m ∈ Finset.Icc 1 (⌊2 * R⌋₊ / d),
      Real.log (m : ℝ) * kernel t ((d : ℝ) * m) *
        ((if t < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0) -
          beforeRatio ell R d ((d : ℝ) * m))) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    have h := congrFun hzero ((d : ℝ) * m)
    simpa only [cutRow, mul_div_cancel_left₀ (m : ℝ) hd0.ne'] using h
  unfold latticeRowRemainder
  rw [hsum, hzero]
  simp

/-- The source-specific crossing count consumes the complete row estimate: every
    noncrossing divisor row is literally zero, and all remaining integer rows are
    paid with the actual Möbius absolute value. -/
theorem original_cut_row_pointwise_budget {ell R t : ℝ}
    (hell : 256 ≤ ell) (horder : ell < R) (ht : t ∈ Icc ell R) :
    ∑ d ∈ Finset.Icc 1 (⌊endpoint t ^ (151 / 500 : ℝ)⌋₊),
      |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
        |latticeRowRemainder ell R t d| ≤
      6 * t ^ (-99 / 500 : ℝ) * Real.log (2 * t) := by
  have ht256 : 256 ≤ t := hell.trans ht.1
  have ht4 : 4 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  let A : Finset ℕ := Finset.Icc 1 (⌊endpoint t ^ (151 / 500 : ℝ)⌋₊)
  let C : Finset ℕ := Finset.Icc
    (⌊lowerClock t ^ (151 / 500 : ℝ)⌋₊ + 1)
    (⌊endpoint t ^ (151 / 500 : ℝ)⌋₊)
  let f : ℕ → ℝ := fun d =>
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
      |latticeRowRemainder ell R t d|
  have hCsub : C ⊆ A := by
    intro d hd
    simp only [C, A, Finset.mem_Icc] at hd ⊢
    exact ⟨by omega, hd.2⟩
  have hzero_out : ∀ d ∈ A, d ∉ C → f d = 0 := by
    intro d hdA hdC
    have hdA' : 1 ≤ d ∧ d ≤ ⌊endpoint t ^ (151 / 500 : ℝ)⌋₊ :=
      Finset.mem_Icc.mp hdA
    have hd1 : 1 ≤ d := hdA'.1
    have hdupper : d ≤ ⌊endpoint t ^ (151 / 500 : ℝ)⌋₊ := hdA'.2
    have hdlower : d ≤ ⌊lowerClock t ^ (151 / 500 : ℝ)⌋₊ := by
      by_contra hnot
      have hge : ⌊lowerClock t ^ (151 / 500 : ℝ)⌋₊ + 1 ≤ d := by omega
      apply hdC
      exact Finset.mem_Icc.mpr ⟨hge, hdupper⟩
    have hcut : (d : ℝ) ≤ lowerClock t ^ (151 / 500 : ℝ) :=
      (Nat.cast_le.2 hdlower).trans
        (Nat.floor_le (Real.rpow_nonneg (lowerClock_bounds ht256).1.le _))
    have hzero : cutRow ell R t d = fun _ => 0 := by
      funext x
      exact cutRow_zero_below hell horder ht hd1 hcut x
    dsimp [f]
    rw [latticeRowRemainder_zero_of_cutRow hd1 hzero, abs_zero, mul_zero]
  have hsum_eq : (∑ d ∈ A, f d) = (∑ d ∈ C, f d) := by
    symm
    exact Finset.sum_subset hCsub hzero_out
  have hterm : ∀ d ∈ C, f d ≤
      3 * lowerHeight t * Real.log (2 * t) := by
    intro d hdC
    have hd1 : 1 ≤ d := by
      have hbounds := Finset.mem_Icc.mp hdC
      omega
    have hμZ := ArithmeticFunction.abs_moebius_le_one (n := d)
    have hμ : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast hμZ
    have hrow := original_cut_row_lattice_estimate hell horder ht hd1
    dsimp [f]
    calc
      |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
          |latticeRowRemainder ell R t d| ≤
          1 * |latticeRowRemainder ell R t d| :=
        mul_le_mul_of_nonneg_right hμ (abs_nonneg _)
      _ ≤ 1 * (3 * lowerHeight t * Real.log (2 * t)) :=
        mul_le_mul_of_nonneg_left hrow (by norm_num)
      _ = 3 * lowerHeight t * Real.log (2 * t) := by ring
  change (∑ d ∈ A, f d) ≤ _
  rw [hsum_eq]
  calc
    _ ≤ ∑ _d ∈ C, (3 * lowerHeight t * Real.log (2 * t)) :=
      Finset.sum_le_sum hterm
    _ = (C.card : ℝ) * (3 * lowerHeight t * Real.log (2 * t)) := by simp
    _ ≤ (2 * t ^ (51 / 500 : ℝ)) *
        (3 * lowerHeight t * Real.log (2 * t)) := by
      have hnonneg : 0 ≤ 3 * lowerHeight t * Real.log (2 * t) := by
        exact mul_nonneg (mul_nonneg (by norm_num) (height_bounds ht4).1)
          (Real.log_nonneg (by linarith))
      apply mul_le_mul_of_nonneg_right _ hnonneg
      have hcard : (C.card : ℝ) ≤ 2 * t ^ (51 / 500 : ℝ) := by
        dsimp [C]
        exact_mod_cast crossing_count ht256
      exact hcard
    _ ≤ 6 * t ^ (-99 / 500 : ℝ) * Real.log (2 * t) := by
      have hb := (height_bounds ht4).2
      have hlog : 0 ≤ Real.log (2 * t) := Real.log_nonneg (by linarith)
      have hpow : t ^ (51 / 500 : ℝ) * t ^ (-3 / 10 : ℝ) =
          t ^ (-99 / 500 : ℝ) := by
        rw [← Real.rpow_add ht0]
        norm_num
      have hbase : t ^ (51 / 500 : ℝ) * lowerHeight t ≤
          t ^ (-99 / 500 : ℝ) := by
        calc
          t ^ (51 / 500 : ℝ) * lowerHeight t ≤
              t ^ (51 / 500 : ℝ) * t ^ (-3 / 10 : ℝ) :=
            mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg ht0.le _)
          _ = t ^ (-99 / 500 : ℝ) := hpow
      calc
        (2 * t ^ (51 / 500 : ℝ)) *
            (3 * lowerHeight t * Real.log (2 * t)) =
            6 * (t ^ (51 / 500 : ℝ) * lowerHeight t) * Real.log (2 * t) := by
          ring
        _ ≤ 6 * t ^ (-99 / 500 : ℝ) * Real.log (2 * t) := by
          gcongr

/-- The literal signed moving-cut lattice contribution, with all positive
    integer pairs whose product is at most the complete support bound. -/
def cutLattice (ell R : ℝ) (S : Set ℝ) : ℝ :=
  ∫ t in S, ∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      ∑ m ∈ Finset.Icc 1 (⌊2 * R⌋₊ / d),
        Real.log (m : ℝ) * kernel t ((d : ℝ) * m) *
          ((if t < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0) -
            beforeRatio ell R d ((d : ℝ) * m))

/-- The original time-dependent continuous divisor sum. -/
def divisorPosterior (t x : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ⌊t ^ (151 / 500 : ℝ)⌋₊,
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (x / d) / d

/-- The kernel-weighted posterior on the complete reference interval;
    division at zero mass is the real zero convention. -/
def averagedPosterior (ell R x : ℝ) : ℝ :=
  (∫ s in Icc ell R, kernel s x * divisorPosterior s x) / windowMass ell R x

/-- The literal posterior correction, integrated on the original moving windows. -/
def cutPosterior (ell R : ℝ) (S : Set ℝ) : ℝ :=
  ∫ t in S, ∫ x in t..endpoint t,
    kernel t x * (divisorPosterior t x - averagedPosterior ell R x)

private lemma measurable_kernel_joint : Measurable (fun p : ℝ × ℝ => kernel p.1 p.2) := by
  unfold kernel g weight endpoint width
  apply Measurable.ite
  · exact (measurableSet_lt measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd
        (show Measurable (fun p : ℝ × ℝ => p.1 + p.1 ^ (4 / 5 : ℝ)) by fun_prop))
  · fun_prop
  · exact measurable_const

private lemma measurable_windowMass (ell R : ℝ) : Measurable (windowMass ell R) :=
  (measurable_kernel_joint.stronglyMeasurable.integral_prod_left'
    (μ := volume.restrict (Icc ell R))).measurable

private lemma measurable_beforeMass (ell R : ℝ) (d : ℕ) :
    Measurable (beforeMass ell R d) :=
  (measurable_kernel_joint.stronglyMeasurable.integral_prod_left'
    (μ := volume.restrict (Icc ell R ∩ Iio ((d : ℝ) ^ (500 / 151 : ℝ))))).measurable

private lemma measurable_beforeRatio (ell R : ℝ) (d : ℕ) :
    Measurable (beforeRatio ell R d) :=
  (measurable_beforeMass ell R d).div (measurable_windowMass ell R)

private lemma measurable_cutRow_joint (ell R : ℝ) (d : ℕ) :
    Measurable (fun p : ℝ × ℝ => cutRow ell R p.1 d p.2) := by
  unfold cutRow
  exact ((measurable_snd.div_const (d : ℝ)).log.mul measurable_kernel_joint).mul
    ((measurable_const.ite (measurableSet_lt measurable_fst measurable_const)
      measurable_const).sub ((measurable_beforeRatio ell R d).comp measurable_snd))

private lemma beforeRatio_bounds_all {ell R x : ℝ} (hell : 4 ≤ ell) (d : ℕ) :
    beforeRatio ell R d x ∈ Icc 0 1 := by
  have hK : 0 ≤ windowMass ell R x := by
    apply setIntegral_nonneg measurableSet_Icc
    intro s hs
    exact kernel_nonneg (hell.trans hs.1)
  rcases hK.eq_or_lt with hz | hp
  · simp [beforeRatio, ← hz]
  · exact beforeRatio_bounds hell d hp

private lemma cutoff_indicator {t : ℝ} (ht : 0 ≤ t) {d : ℕ} (hd : 1 ≤ d) :
    d ≤ ⌊t ^ (151 / 500 : ℝ)⌋₊ ↔ ¬t < (d : ℝ) ^ (500 / 151 : ℝ) := by
  rw [Nat.le_floor_iff (Real.rpow_nonneg ht _), not_lt]
  constructor
  · intro h
    calc
      (d : ℝ) ^ (500 / 151 : ℝ) ≤
          (t ^ (151 / 500 : ℝ)) ^ (500 / 151 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg d) h (by norm_num)
      _ = t := by rw [← Real.rpow_mul ht]; norm_num
  · intro h
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg d) _) h
      (by norm_num : (0 : ℝ) ≤ 151 / 500)
    simpa only [← Real.rpow_mul (Nat.cast_nonneg d),
      show (500 / 151 : ℝ) * (151 / 500 : ℝ) = 1 by norm_num,
      Real.rpow_one] using hh

private lemma posterior_fixed_sum {R t x : ℝ} (ht : 256 ≤ t) (htR : t ≤ R) :
    divisorPosterior t x = ∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (x / d) / d *
        (1 - if t < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0) := by
  have hsmall : t ^ (151 / 500 : ℝ) ≤ 2 * R :=
    (Real.rpow_le_self_of_one_le (by linarith) (by norm_num)).trans (by linarith)
  have hsub : Finset.Icc 1 ⌊t ^ (151 / 500 : ℝ)⌋₊ ⊆ Finset.Icc 1 ⌊2 * R⌋₊ := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
      (Finset.mem_Icc.mp hd).2.trans (Nat.floor_mono hsmall)⟩
  unfold divisorPosterior
  calc
    _ = ∑ d ∈ Finset.Icc 1 ⌊t ^ (151 / 500 : ℝ)⌋₊,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (x / d) / d *
          (1 - if t < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hd' := Finset.mem_Icc.mp hd
      simp [(cutoff_indicator (by linarith) hd'.1).mp hd'.2]
    _ = _ := Finset.sum_subset hsub (by
      intro d hd hnot
      have hd1 := (Finset.mem_Icc.mp hd).1
      have hcut : t < (d : ℝ) ^ (500 / 151 : ℝ) := by
        by_contra h
        exact hnot (Finset.mem_Icc.mpr ⟨hd1,
          (cutoff_indicator (by linarith) hd1).mpr h⟩)
      simp [hcut])

private lemma cutRow_integral_fixed {ell R t : ℝ}
    (hell : 256 ≤ ell) (ht : t ∈ Icc ell R) (d : ℕ) :
    (∫ x in t..endpoint t, cutRow ell R t d x) =
      ∫ x in Icc 0 (2 * R), cutRow ell R t d x := by
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have htb : t ≤ endpoint t := le_add_of_nonneg_right (Real.rpow_nonneg ht0 _)
  have hb : endpoint t ≤ 2 * R := (endpoint_le_twice (by linarith [ht.1])).trans (by linarith [ht.2])
  rw [intervalIntegral.integral_of_le htb]
  symm
  apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Icc.nullMeasurableSet
  · intro x hx
    exact ⟨ht0.trans hx.1.le, hx.2.trans hb⟩
  · filter_upwards [] with x hx
    apply cutRow_zero_of_outside d
    by_cases hxt : x ≤ t
    · exact Or.inl hxt
    · exact Or.inr (le_of_lt (lt_of_not_ge (by
        intro hxb
        exact hx.2 ⟨not_le.mp hxt, hxb⟩)))

private lemma averagedPosterior_fixed_sum {ell R x : ℝ} (hell : 256 ≤ ell)
    (hK : windowMass ell R x ≠ 0) :
    averagedPosterior ell R x = ∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (x / d) / d *
        (1 - beforeRatio ell R d x) := by
  let A : ℕ → ℝ := fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    Real.log (x / d) / d
  have hi : IntegrableOn (fun s => kernel s x) (Icc ell R) :=
    kernel_integrableOn (by linarith)
  have hj : ∀ d : ℕ, IntegrableOn (fun s => kernel s x *
      (if s < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0)) (Icc ell R) := by
    intro d
    have heq : (fun s => kernel s x *
        (if s < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0)) =
        (Iio ((d : ℝ) ^ (500 / 151 : ℝ))).indicator (fun s => kernel s x) := by
      funext s
      simp only [Set.indicator, mem_Iio]
      split_ifs <;> simp
    rw [heq]
    exact hi.indicator measurableSet_Iio
  have hrow : ∀ d : ℕ, IntegrableOn (fun s => kernel s x *
      (1 - if s < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0)) (Icc ell R) := by
    intro d
    simp_rw [mul_sub, mul_one]
    exact hi.sub (hj d)
  have hbefore : ∀ d : ℕ, (∫ s in Icc ell R, kernel s x *
      (if s < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0)) = beforeMass ell R d x := by
    intro d
    unfold beforeMass
    rw [← setIntegral_indicator measurableSet_Iio]
    apply integral_congr_ae
    filter_upwards [] with s
    simp only [Set.indicator, mem_Iio]
    split_ifs <;> simp
  have hsplit : ∀ d : ℕ, (∫ s in Icc ell R, kernel s x *
      (1 - if s < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0)) =
        windowMass ell R x - beforeMass ell R d x := by
    intro d
    simp_rw [mul_sub, mul_one]
    rw [integral_sub hi (hj d), hbefore]
    rfl
  unfold averagedPosterior
  have hexpand : (∫ s in Icc ell R, kernel s x * divisorPosterior s x) =
      ∫ s in Icc ell R, ∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
        A d * (kernel s x * (1 - if s < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0)) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    dsimp only
    rw [posterior_fixed_sum (hell.trans hs.1) hs.2, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    dsimp [A]
    ring
  rw [hexpand, integral_finsetSum _ (fun d _ => (hrow d).const_mul (A d))]
  simp_rw [integral_const_mul, hsplit, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  dsimp [A, beforeRatio]
  field_simp [hK]

private lemma posterior_weighted_identity {ell R t : ℝ}
    (hell : 256 ≤ ell) (horder : ell < R) (ht : t ∈ Icc ell R) (x : ℝ) :
    kernel t x * (divisorPosterior t x - averagedPosterior ell R x) =
      -∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * cutRow ell R t d x / d := by
  by_cases hz : kernel t x = 0
  · simp [hz, cutRow]
  have hk : 0 < kernel t x := lt_of_le_of_ne (kernel_nonneg (by linarith [ht.1]))
    (Ne.symm hz)
  have hK := windowMass_pos_of_kernel_pos (by linarith) horder ht hk
  rw [posterior_fixed_sum (hell.trans ht.1) ht.2,
    averagedPosterior_fixed_sum hell hK.ne', ← Finset.sum_sub_distrib,
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro d _
  unfold cutRow
  ring

private lemma cutRow_uniform_bound {ell R t : ℝ} (hell : 256 ≤ ell)
    (ht : t ∈ Icc ell R) {d : ℕ} (hd : 1 ≤ d) (x : ℝ) :
    ‖cutRow ell R t d x‖ ≤ Real.log (2 * R) + Real.log d := by
  have ht4 : 4 ≤ t := by linarith [ht.1]
  have hR : 1 ≤ 2 * R := by linarith [ht.1, ht.2]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hlogd : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  have hC : 0 ≤ Real.log (2 * R) + Real.log d :=
    add_nonneg (Real.log_nonneg hR) hlogd
  by_cases hz : kernel t x = 0
  · simpa [cutRow, hz] using hC
  have hk := (kernel_pos_iff ht4).mp
    (lt_of_le_of_ne (kernel_nonneg ht4) (Ne.symm hz))
  have hx0 : 0 < x := by linarith [ht.1, hk.1]
  have hxR : x ≤ 2 * R := hk.2.le.trans
    ((endpoint_le_twice (by linarith)).trans (by linarith [ht.2]))
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith [ht.1, hk.1])
  have hlogupper := Real.log_le_log hx0 hxR
  have hl : |Real.log (x / d)| ≤ Real.log (2 * R) + Real.log d := by
    rw [Real.log_div hx0.ne' hd0.ne', abs_le]
    constructor <;> linarith
  have hr := beforeRatio_bounds_all (ell := ell) (R := R) (x := x) (by linarith) d
  have hc : |(if t < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0) -
      beforeRatio ell R d x| ≤ 1 := by
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith [hr.1, hr.2]
  rw [Real.norm_eq_abs, cutRow, abs_mul, abs_mul,
    abs_of_nonneg (kernel_nonneg ht4)]
  calc
    _ ≤ (Real.log (2 * R) + Real.log d) * 1 * 1 := by
      gcongr <;> first | exact kernel_le_one ht4 | exact kernel_nonneg ht4
    _ = _ := by ring

private lemma cutRow_integrable_fixed {ell R t : ℝ} (hell : 256 ≤ ell)
    (ht : t ∈ Icc ell R) {d : ℕ} (hd : 1 ≤ d) :
    IntegrableOn (cutRow ell R t d) (Icc 0 (2 * R)) := by
  apply (integrableOn_const (C := Real.log (2 * R) + Real.log d) isCompact_Icc.measure_ne_top).mono'
    (((measurable_cutRow_joint ell R d).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  filter_upwards [] with x
  exact cutRow_uniform_bound hell ht hd x

private lemma cutRow_intervalIntegrable {ell R t : ℝ} (hell : 256 ≤ ell)
    (ht : t ∈ Icc ell R) {d : ℕ} (hd : 1 ≤ d) :
    IntervalIntegrable (cutRow ell R t d) volume t (endpoint t) := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (show t ≤ endpoint t from
      le_add_of_nonneg_right (Real.rpow_nonneg (by linarith [ht.1]) _))).2
  apply (cutRow_integrable_fixed hell ht hd).mono_set
  intro x hx
  exact ⟨le_trans (by linarith [ht.1]) hx.1.le, hx.2.trans
    ((endpoint_le_twice (by linarith [ht.1])).trans (by linarith [ht.2]))⟩

private lemma cutRow_integral_integrableOn {ell R : ℝ} (hell : 256 ≤ ell)
    {d : ℕ} (hd : 1 ≤ d) :
    IntegrableOn (fun t => ∫ x in t..endpoint t, cutRow ell R t d x) (Icc ell R) := by
  have hm : Measurable (fun t => ∫ x in Icc 0 (2 * R), cutRow ell R t d x) :=
    ((measurable_cutRow_joint ell R d).stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Icc 0 (2 * R)))).measurable
  have hi : IntegrableOn (fun t => ∫ x in Icc 0 (2 * R), cutRow ell R t d x)
      (Icc ell R) := by
    apply (integrableOn_const
      (C := (Real.log (2 * R) + Real.log d) * (volume (Icc 0 (2 * R))).toReal)
      (by simp)).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact norm_setIntegral_le_of_norm_le_const isCompact_Icc.measure_lt_top
      (fun x _ => cutRow_uniform_bound hell ht hd x)
  apply hi.congr_fun (fun t ht => (cutRow_integral_fixed hell ht d).symm)
    measurableSet_Icc

private def latticePart (ell R t : ℝ) (d : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (⌊2 * R⌋₊ / d),
    Real.log (m : ℝ) * kernel t ((d : ℝ) * m) *
      ((if t < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0) -
        beforeRatio ell R d ((d : ℝ) * m))

private lemma latticePart_eq {ell R t : ℝ} {d : ℕ} (hd : 1 ≤ d) :
    latticePart ell R t d = ∑ m ∈ Finset.Icc 1 (⌊2 * R⌋₊ / d),
      cutRow ell R t d ((d : ℝ) * m) := by
  apply Finset.sum_congr rfl
  intro m _
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  simp only [cutRow, mul_div_cancel_left₀ _ hd0]

private lemma latticePart_integrableOn {ell R : ℝ} (hell : 256 ≤ ell)
    {d : ℕ} (hd : 1 ≤ d) : IntegrableOn (fun t => latticePart ell R t d) (Icc ell R) := by
  simp_rw [latticePart_eq hd]
  apply integrable_finsetSum
  intro m _
  apply (integrableOn_const (C := Real.log (2 * R) + Real.log d)
    isCompact_Icc.measure_ne_top).mono'
    (((measurable_cutRow_joint ell R d).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact cutRow_uniform_bound hell ht hd _

private lemma posterior_integral_identity {ell R t : ℝ}
    (hell : 256 ≤ ell) (horder : ell < R) (ht : t ∈ Icc ell R) :
    (∫ x in t..endpoint t,
      kernel t x * (divisorPosterior t x - averagedPosterior ell R x)) =
        -(∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
            (∫ x in t..endpoint t, cutRow ell R t d x) / d) := by
  have heq : (fun x => kernel t x *
      (divisorPosterior t x - averagedPosterior ell R x)) =
      fun x => -(∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * cutRow ell R t d x / d) := by
    funext x
    exact posterior_weighted_identity hell horder ht x
  rw [heq, intervalIntegral.integral_neg, intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul]
  · intro d hd
    exact ((cutRow_intervalIntegrable hell ht (Finset.mem_Icc.mp hd).1).const_mul _).div_const _

private lemma cut_aggregate_identity {ell R : ℝ} (hell : 256 ≤ ell) (horder : ell < R)
    {S : Set ℝ} (hS : MeasurableSet S) (hSJ : S ⊆ Icc ell R) :
    cutLattice ell R S + cutPosterior ell R S =
      ∫ t in S, ∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * latticeRowRemainder ell R t d := by
  let A : ℝ → ℝ := fun t => ∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) * latticePart ell R t d
  let B : ℝ → ℝ := fun t => ∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      (∫ x in t..endpoint t, cutRow ell R t d x) / d
  have hAJ : IntegrableOn A (Icc ell R) := by
    dsimp [A]
    exact integrable_finsetSum _ (fun d hd =>
      (latticePart_integrableOn hell (Finset.mem_Icc.mp hd).1).const_mul _)
  have hBJ : IntegrableOn B (Icc ell R) := by
    dsimp [B]
    exact integrable_finsetSum _ (fun d hd =>
      ((cutRow_integral_integrableOn hell (Finset.mem_Icc.mp hd).1).const_mul _).div_const _)
  have hA : IntegrableOn A S := hAJ.mono_set hSJ
  have hB : IntegrableOn B S := hBJ.mono_set hSJ
  have hP : cutPosterior ell R S = -(∫ t in S, B t) := by
    unfold cutPosterior
    rw [← integral_neg]
    apply setIntegral_congr_fun hS
    intro t ht
    dsimp [B]
    exact posterior_integral_identity hell horder (hSJ ht)
  change (∫ t in S, A t) + cutPosterior ell R S = _
  rw [hP, ← sub_eq_add_neg, ← integral_sub hA hB]
  apply setIntegral_congr_fun hS
  intro t _
  dsimp [A, B]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  change _ = _ * (latticePart ell R t d - _)
  ring

private lemma row_zero_past_cutoff {ell R t : ℝ} (hell : 256 ≤ ell)
    (horder : ell < R) (ht : t ∈ Icc ell R) {d : ℕ} (hd : 1 ≤ d)
    (hcut : ⌊endpoint t ^ (151 / 500 : ℝ)⌋₊ < d) :
    latticeRowRemainder ell R t d = 0 := by
  apply latticeRowRemainder_zero_of_cutRow hd
  funext x
  apply cutRow_zero_above hell horder ht _ x
  have hB : 0 ≤ endpoint t := by
    have hw := Real.rpow_nonneg (by linarith [ht.1] : 0 ≤ t) (4 / 5 : ℝ)
    dsimp [endpoint, width]
    linarith [ht.1]
  exact ((Nat.floor_lt (Real.rpow_nonneg hB _)).mp hcut).le

private lemma signed_cut_bound {ell R t : ℝ} (hell : 256 ≤ ell)
    (horder : ell < R) (ht : t ∈ Icc ell R) :
    |∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * latticeRowRemainder ell R t d| ≤
        6 * t ^ (-99 / 500 : ℝ) * Real.log (2 * t) := by
  have hB : 1 ≤ endpoint t := by
    have hw := Real.rpow_nonneg (by linarith [ht.1] : 0 ≤ t) (4 / 5 : ℝ)
    dsimp [endpoint, width]
    linarith [ht.1]
  have hsmall : endpoint t ^ (151 / 500 : ℝ) ≤ 2 * R :=
    (Real.rpow_le_self_of_one_le hB (by norm_num)).trans
      ((endpoint_le_twice (by linarith [ht.1])).trans (by linarith [ht.2]))
  have hsub : Finset.Icc 1 ⌊endpoint t ^ (151 / 500 : ℝ)⌋₊ ⊆
      Finset.Icc 1 ⌊2 * R⌋₊ := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
      (Finset.mem_Icc.mp hd).2.trans (Nat.floor_mono hsmall)⟩
  have heq : (∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
      |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * |latticeRowRemainder ell R t d|) =
      ∑ d ∈ Finset.Icc 1 ⌊endpoint t ^ (151 / 500 : ℝ)⌋₊,
        |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * |latticeRowRemainder ell R t d| := by
    symm
    apply Finset.sum_subset hsub
    intro d hd hnot
    have hd1 := (Finset.mem_Icc.mp hd).1
    have hcut : ⌊endpoint t ^ (151 / 500 : ℝ)⌋₊ < d := by
      by_contra h
      exact hnot (Finset.mem_Icc.mpr ⟨hd1, not_lt.mp h⟩)
    rw [row_zero_past_cutoff hell horder ht hd1 hcut, abs_zero, mul_zero]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
        |((ArithmeticFunction.moebius d : ℤ) : ℝ) * latticeRowRemainder ell R t d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
        |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
          |latticeRowRemainder ell R t d| := by simp_rw [abs_mul]
    _ ≤ _ := by rw [heq]; exact original_cut_row_pointwise_budget hell horder ht

private lemma log_power_antitone :
    AntitoneOn (fun t : ℝ => t ^ (-99 / 500 : ℝ) * Real.log (2 * t)) (Ici 256) := by
  have hbase : 500 / 99 < Real.log (512 : ℝ) := by
    have heq := Real.log_pow (2 : ℝ) 9
    norm_num at heq
    linarith [Real.log_two_gt_d9]
  have hD : ∀ x ∈ Ici (256 : ℝ), HasDerivAt
      (fun t : ℝ => t ^ (-99 / 500 : ℝ) * Real.log (2 * t))
      (x ^ (-99 / 500 - 1 : ℝ) * (1 - 99 / 500 * Real.log (2 * x))) x := by
    intro x hx
    change 256 ≤ x at hx
    have hx0 : 0 < x := by linarith
    have hp : x ^ (-99 / 500 : ℝ) = x ^ (-99 / 500 - 1 : ℝ) * x := by
      calc
        _ = x ^ ((-99 / 500 - 1 : ℝ) + 1) := by congr 1; norm_num
        _ = _ := by rw [Real.rpow_add hx0, Real.rpow_one]
    convert ((Real.hasDerivAt_rpow_const (p := (-99 / 500 : ℝ)) (Or.inl hx0.ne')).mul
      ((Real.hasDerivAt_log (by positivity : 2 * x ≠ 0)).comp x
        ((hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_id x)))) using 1
    <;> first | rfl | (rw [hp]; field_simp; ring_nf; simp only [Function.comp_apply, mul_comm])
  have hn : ∀ x ∈ Ici (256 : ℝ),
      x ^ (-99 / 500 - 1 : ℝ) * (1 - 99 / 500 * Real.log (2 * x)) ≤ 0 := by
    intro x hx
    change 256 ≤ x at hx
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 512)
      (show (512 : ℝ) ≤ 2 * x by linarith [hx])
    apply mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (by linarith [hx]) _)
    linarith
  exact antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici _)
    (HasDerivAt.continuousOn hD)
    (fun x hx => (hD x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => hn x (interior_subset hx))

/-- The original lattice cut and posterior cut have the complete finite-Fubini
    identity and an arbitrary-measurable-set bound with the original volume. -/
theorem original_cut_aggregate_estimate {ell R : ℝ} (hell : 256 ≤ ell)
    (horder : ell < R) {S : Set ℝ} (hS : MeasurableSet S) (hSJ : S ⊆ Icc ell R)
    (hM : 0 < (volume S).toReal) :
    cutLattice ell R S + cutPosterior ell R S =
        (∫ t in S, ∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) * latticeRowRemainder ell R t d) ∧
    |cutLattice ell R S + cutPosterior ell R S| ≤
        6 * (∫ t in S, t ^ (-99 / 500 : ℝ) * Real.log (2 * t)) ∧
    6 * (∫ t in S, t ^ (-99 / 500 : ℝ) * Real.log (2 * t)) ≤
        6 * (volume S).toReal * ell ^ (-99 / 500 : ℝ) * Real.log (2 * ell) := by
  have hid := cut_aggregate_identity hell horder hS hSJ
  have hfin : volume S ≠ ⊤ := ne_top_of_le_ne_top isCompact_Icc.measure_ne_top
    (measure_mono hSJ)
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-99 / 500 : ℝ) * Real.log (2 * t))
      (Icc ell R) := by
    apply ContinuousOn.mul
    · exact continuousOn_id.rpow_const (fun t ht => Or.inl (by
        change t ≠ 0
        linarith [ht.1]))
    · exact (continuousOn_const.mul continuousOn_id).log
        (fun t ht => by change 2 * t ≠ 0; linarith [ht.1])
  have hi : IntegrableOn (fun t : ℝ => t ^ (-99 / 500 : ℝ) * Real.log (2 * t)) S :=
    (hcont.integrableOn_Icc).mono_set hSJ
  refine ⟨hid, ?_, ?_⟩
  · rw [hid]
    have hb := norm_integral_le_of_norm_le
      (f := fun t => ∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * latticeRowRemainder ell R t d)
      (hi.const_mul 6) (by
      filter_upwards [ae_restrict_mem hS] with t ht
      rw [Real.norm_eq_abs]
      simpa only [mul_assoc] using signed_cut_bound hell horder (hSJ ht))
    simpa only [Real.norm_eq_abs, integral_const_mul] using hb
  · have hle : (∫ t in S, t ^ (-99 / 500 : ℝ) * Real.log (2 * t)) ≤
        (volume S).toReal * (ell ^ (-99 / 500 : ℝ) * Real.log (2 * ell)) := by
      calc
        _ ≤ ∫ _t in S, ell ^ (-99 / 500 : ℝ) * Real.log (2 * ell) :=
          setIntegral_mono_on hi (integrableOn_const hfin) hS (fun t ht =>
            log_power_antitone hell (hell.trans (hSJ ht).1) (hSJ ht).1)
        _ = _ := by rw [setIntegral_const, smul_eq_mul]; rfl
    nlinarith

#print axioms original_cut_aggregate_estimate
#print axioms original_cut_row_lattice_estimate

end D5.S3.Arith.Robin.OriginalMovingWindowMoment

#print axioms D5.S3.Arith.Robin.OriginalMovingWindowMoment.original_window_moment_estimate
