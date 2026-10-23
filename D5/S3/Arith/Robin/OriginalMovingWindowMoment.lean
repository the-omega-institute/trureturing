/- GID: D5/S3/Arith/Robin/OriginalMovingWindowMoment
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/OriginalMovingWindowMoment
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: The original reciprocal-logarithmic moving window has explicit decaying moment bounds. -/

import D5.S3.Arith.Robin.MellinWeightedVariation
import D5.S3.Arith.Robin.LogarithmBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
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

lemma weight_pos {x : ℝ} (hx : 1 < x) : 0 < weight x := by
  unfold weight
  positivity [Real.log_pos hx]

lemma log_large {x : ℝ} (hx : 4 ≤ x) : 1 ≤ Real.log x := by
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

lemma price_drop {t x b : ℝ} (ht : 4 ≤ t) (htx : t ≤ x) (hxb : x ≤ b) :
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

end D5.S3.Arith.Robin.OriginalMovingWindowMoment

#print axioms D5.S3.Arith.Robin.OriginalMovingWindowMoment.original_window_moment_estimate
