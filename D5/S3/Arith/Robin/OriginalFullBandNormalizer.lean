/- GID: D5/S3/Arith/Robin/OriginalFullBandNormalizer
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/OriginalFullBandNormalizer
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: The literal source-clock full-band mass has a positive square-root envelope. -/

import D5.S3.Arith.Robin.OriginalMovingCutRow
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The literal reciprocal-log kernel has a positive source-clock full-band envelope. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set
open D5.S3.Arith.Robin.MellinWeightedVariation (weight)
open D5.S3.Arith.Robin.ActualRobinClockCovariance (g)
open D5.S3.Arith.Robin.OriginalMovingWindowMoment
open D5.S3.Arith.Robin.OriginalMovingCutRow

namespace D5.S3.Arith.Robin.OriginalFullBandNormalizer

private lemma endpoint_factor {t : ℝ} (ht : 0 < t) :
    endpoint t = t * (1 + t ^ (-1 / 5 : ℝ)) := by
  have hw : width t = t * t ^ (-1 / 5 : ℝ) := by
    dsimp [width]
    simpa only [show (1 : ℝ) + -1 / 5 = 4 / 5 by norm_num, Real.rpow_one]
      using (Real.rpow_add ht (1 : ℝ) (-1 / 5 : ℝ))
  simp only [endpoint, hw]
  ring

private lemma endpoint_ratio_mono {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) :
    a / endpoint a ≤ t / endpoint t := by
  have ht : 0 < t := ha.trans_le hat
  have hpow := Real.rpow_le_rpow_of_nonpos ha hat (by norm_num : (-1 / 5 : ℝ) ≤ 0)
  have hratio (s : ℝ) (hs : 0 < s) :
      s / endpoint s = 1 / (1 + s ^ (-1 / 5 : ℝ)) := by
    rw [endpoint_factor hs]
    field_simp [hs.ne']
  rw [hratio a ha, hratio t ht]
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- Both secants are taken in the source clock, up to the observation x. -/
private lemma endpoint_secants {a t x : ℝ} (ha : 0 < a)
    (hat : a ≤ t) (htx : t ≤ x) :
    (1 + (4 / 5 : ℝ) * x ^ (-1 / 5 : ℝ)) * (t - a) ≤ endpoint t - endpoint a ∧
    endpoint t - endpoint a ≤ (1 + (4 / 5 : ℝ) * a ^ (-1 / 5 : ℝ)) * (t - a) := by
  have hax := hat.trans htx
  have hd : ∀ s ∈ Icc a x, HasDerivAt endpoint
      (1 + (4 / 5 : ℝ) * s ^ (-1 / 5 : ℝ)) s := by
    intro s hs
    have hs0 : 0 < s := ha.trans_le hs.1
    simpa only [endpoint, width, id_eq,
      show (4 / 5 : ℝ) - 1 = -1 / 5 by norm_num] using!
      (hasDerivAt_id s).add
        (Real.hasDerivAt_rpow_const (p := (4 / 5 : ℝ)) (Or.inl hs0.ne'))
  let L : ℝ := 1 + (4 / 5 : ℝ) * x ^ (-1 / 5 : ℝ)
  let U : ℝ := 1 + (4 / 5 : ℝ) * a ^ (-1 / 5 : ℝ)
  have hdL : ∀ s ∈ Icc a x, HasDerivAt (fun y => endpoint y - L * y)
      (1 + (4 / 5 : ℝ) * s ^ (-1 / 5 : ℝ) - L) s := by
    intro s hs
    simpa only [mul_one] using! (hd s hs).sub ((hasDerivAt_id s).const_mul L)
  have hdU : ∀ s ∈ Icc a x, HasDerivAt (fun y => endpoint y - U * y)
      (1 + (4 / 5 : ℝ) * s ^ (-1 / 5 : ℝ) - U) s := by
    intro s hs
    simpa only [mul_one] using! (hd s hs).sub ((hasDerivAt_id s).const_mul U)
  have hmL := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a x)
    (HasDerivAt.continuousOn hdL)
    (fun s hs => (hdL s (interior_subset hs)).hasDerivWithinAt)
    (by
      intro s hs
      have hs' := interior_subset hs
      have hp := Real.rpow_le_rpow_of_nonpos (ha.trans_le hs'.1) hs'.2
        (by norm_num : (-1 / 5 : ℝ) ≤ 0)
      dsimp [L]
      linarith)
  have hmU := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a x)
    (HasDerivAt.continuousOn hdU)
    (fun s hs => (hdU s (interior_subset hs)).hasDerivWithinAt)
    (by
      intro s hs
      have hs' := interior_subset hs
      have hp := Real.rpow_le_rpow_of_nonpos ha hs'.1
        (by norm_num : (-1 / 5 : ℝ) ≤ 0)
      dsimp [U]
      linarith)
  have hL := hmL (left_mem_Icc.mpr hax) ⟨hat, htx⟩ hat
  have hU := hmU (left_mem_Icc.mpr hax) ⟨hat, htx⟩ hat
  dsimp [L, U] at hL hU
  constructor <;> nlinarith

/-- The logarithmic part of y^2 w(y) decreases on the original positive domain. -/
private lemma weight_square_upper {t y : ℝ} (ht : 1 < t) (hty : t ≤ y) :
    weight y ≤ (t / y) ^ 2 * weight t := by
  have ht0 : 0 < t := by linarith
  have hy0 : 0 < y := ht0.trans_le hty
  have hl := Real.log_pos ht
  have hly := Real.log_pos (ht.trans_le hty)
  have hlog := Real.log_le_log ht0 hty
  have h1 := one_div_le_one_div_of_le hl hlog
  have h2 := one_div_le_one_div_of_le (sq_pos_of_pos hl)
    (show Real.log t ^ 2 ≤ Real.log y ^ 2 by nlinarith)
  have hid (s : ℝ) (hs : 0 < s) (hls : 0 < Real.log s) :
      s ^ 2 * weight s = 1 / Real.log s + 1 / Real.log s ^ 2 := by
    unfold weight
    field_simp [hs.ne', hls.ne']
  have hscaled : y ^ 2 * weight y ≤ t ^ 2 * weight t := by
    rw [hid y hy0 hly, hid t ht0 hl]
    exact add_le_add h1 h2
  calc
    weight y = (y ^ 2 * weight y) / y ^ 2 := by field_simp [hy0.ne']
    _ ≤ (t ^ 2 * weight t) / y ^ 2 :=
      div_le_div_of_nonneg_right hscaled (sq_nonneg y)
    _ = (t / y) ^ 2 * weight t := by rw [div_pow]; ring

/-- Integrate the improved weight comparison against the actual price derivative. -/
private lemma price_drop_sharp {t x b : ℝ} (ht : 4 ≤ t) (htx : t ≤ x) (hxb : x ≤ b) :
    g x - g b ≤ (t ^ 2 * weight t) * ((b - x) / (x * b)) := by
  have ht0 : 0 < t := by linarith
  have hx0 : 0 < x := ht0.trans_le htx
  have hb0 : 0 < b := hx0.trans_le hxb
  have hw : IntervalIntegrable weight volume x b := (show ContinuousOn weight (uIcc x b) by
    rw [uIcc_of_le hxb]
    exact weight_continuous (by linarith : 1 < x)).intervalIntegrable
  have hi : IntervalIntegrable (fun y : ℝ => 1 / y ^ 2) volume x b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hxb]
    intro y hy
    exact (continuousAt_const.div (continuousAt_id.pow 2)
      (pow_ne_zero 2 (hx0.trans_le hy.1).ne')).continuousWithinAt
  have hzero : (0 : ℝ) ∉ uIcc x b := by
    rw [uIcc_of_le hxb]
    intro h
    linarith [h.1]
  have hinv : (∫ y in x..b, 1 / y ^ 2) = (b - x) / (x * b) := by
    calc
      _ = ∫ y in x..b, y ^ (-2 : ℤ) := by
        congr 1
        funext y
        simp [zpow_neg, one_div]
      _ = (b ^ (-1 : ℤ) - x ^ (-1 : ℤ)) / (-1 : ℝ) := by
        convert _root_.integral_zpow (a := x) (b := b) (n := (-2 : ℤ))
          (Or.inr ⟨by norm_num, hzero⟩) using 1 <;> norm_num
      _ = _ := by norm_num; field_simp [hx0.ne', hb0.ne'] <;> ring
  calc
    g x - g b = ∫ y in x..b, weight y :=
      (ActualRobinClockCovariance.density_integral (by linarith) hxb).symm
    _ ≤ ∫ y in x..b, (t ^ 2 * weight t) * (1 / y ^ 2) := by
      apply intervalIntegral.integral_mono_on hxb hw (hi.const_mul _)
      intro y hy
      calc
        _ ≤ (t / y) ^ 2 * weight t := weight_square_upper (by linarith) (htx.trans hy.1)
        _ = _ := by rw [div_pow]; ring
    _ = _ := by rw [intervalIntegral.integral_const_mul, hinv]

/-- Write the remaining source factor as z/(z^2+1), with z=t^(1/10)>=1. -/
private lemma source_factor_antitone {a t : ℝ} (ha : 1 ≤ a) (hat : a ≤ t) :
    t ^ (9 / 10 : ℝ) / endpoint t ≤ a ^ (9 / 10 : ℝ) / endpoint a := by
  have ha0 : 0 < a := by linarith
  have ht0 : 0 < t := ha0.trans_le hat
  have hrep (s : ℝ) (hs : 0 < s) :
      s ^ (9 / 10 : ℝ) / endpoint s =
        s ^ (1 / 10 : ℝ) / ((s ^ (1 / 10 : ℝ)) ^ 2 + 1) := by
    have hsq : (s ^ (1 / 10 : ℝ)) ^ 2 = s ^ (1 / 5 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
      norm_num
    have hsum : s ^ (4 / 5 : ℝ) * (s ^ (1 / 5 : ℝ) + 1) = endpoint s := by
      rw [mul_add, ← Real.rpow_add hs]
      norm_num [endpoint, width]
    have hnum : s ^ (9 / 10 : ℝ) = s ^ (4 / 5 : ℝ) * s ^ (1 / 10 : ℝ) := by
      rw [← Real.rpow_add hs]
      norm_num
    rw [hsq, ← hsum, hnum]
    field_simp [(Real.rpow_pos_of_pos hs (4 / 5 : ℝ)).ne']
  have ha1 : 1 ≤ a ^ (1 / 10 : ℝ) := Real.one_le_rpow ha (by norm_num)
  have ht1 : 1 ≤ t ^ (1 / 10 : ℝ) := Real.one_le_rpow (ha.trans hat) (by norm_num)
  have haz := Real.rpow_le_rpow ha0.le hat (by norm_num : (0 : ℝ) ≤ 1 / 10)
  rw [hrep a ha0, hrep t ht0]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hprod : 1 ≤ a ^ (1 / 10 : ℝ) * t ^ (1 / 10 : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr ht1)]
  nlinarith [mul_nonneg (sub_nonneg.mpr haz) (sub_nonneg.mpr hprod)]

private lemma kernel_lower {a t x : ℝ} (ha : 4 ≤ a) (hat : a ≤ t)
    (htx : t < x) (hx : x = endpoint a) :
    x ^ (-11 / 10 : ℝ) * (a / x) ^ 4 *
        (1 + (4 / 5 : ℝ) * x ^ (-1 / 5 : ℝ)) * (t - a) ≤ kernel t x := by
  have ha0 : 0 < a := by linarith
  have ht : 4 ≤ t := ha.trans hat
  have ht0 : 0 < t := ha0.trans_le hat
  have hx0 : 0 < x := ht0.trans htx
  have htb : t ≤ endpoint t := le_add_of_nonneg_right (Real.rpow_nonneg ht0.le _)
  have hxb : x ≤ endpoint t := by
    rw [hx]
    exact endpoint_strictMonoOn.monotoneOn (by simpa using (show 1 ≤ a by linarith))
      (by simpa using (show 1 ≤ t by linarith)) hat
  have hw := weight_pos (by linarith : 1 < t)
  have hden := mul_pos hw (Real.rpow_pos_of_pos ht0 (11 / 10 : ℝ))
  have hp := (price_drop ht htx.le hxb).1
  have hr := weight_ratio_lower ht htb
  have hq : a / x ≤ t / endpoint t := by simpa only [hx] using endpoint_ratio_mono ha0 hat
  have hq4 : (a / x) ^ 4 ≤ (t / endpoint t) ^ 4 := by gcongr
  have hta0 : 0 ≤ t - a := sub_nonneg.mpr hat
  have hb := (endpoint_secants ha0 hat htx.le).1
  rw [← hx] at hb
  have hgap : 0 ≤ endpoint t - x := sub_nonneg.mpr hxb
  have hfirst : (a / x) ^ 4 * weight t * (endpoint t - x) ≤ g x - g (endpoint t) := by
    calc
      _ ≤ (t / endpoint t) ^ 4 * weight t * (endpoint t - x) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hq4 hw.le) hgap
      _ ≤ weight (endpoint t) * (endpoint t - x) := mul_le_mul_of_nonneg_right hr hgap
      _ ≤ _ := hp
  have hn : (a / x) ^ 4 *
      (1 + (4 / 5 : ℝ) * x ^ (-1 / 5 : ℝ)) * (t - a) ≤
      (g x - g (endpoint t)) / weight t := by
    apply (le_div_iff₀ hw).2
    calc
      _ = ((a / x) ^ 4 * weight t) *
          ((1 + (4 / 5 : ℝ) * x ^ (-1 / 5 : ℝ)) * (t - a)) := by ring
      _ ≤ ((a / x) ^ 4 * weight t) * (endpoint t - x) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ _ := hfirst
  have hpower := Real.rpow_le_rpow_of_nonpos ht0 htx.le
    (by norm_num : (-11 / 10 : ℝ) ≤ 0)
  have hbase : 0 ≤ (a / x) ^ 4 *
      (1 + (4 / 5 : ℝ) * x ^ (-1 / 5 : ℝ)) * (t - a) := by positivity
  rw [kernel, ite_eq_left ⟨htx, hxb⟩]
  calc
    _ ≤ t ^ (-11 / 10 : ℝ) * ((a / x) ^ 4 *
        (1 + (4 / 5 : ℝ) * x ^ (-1 / 5 : ℝ)) * (t - a)) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hpower hbase
    _ ≤ t ^ (-11 / 10 : ℝ) * ((g x - g (endpoint t)) / weight t) :=
      mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg ht0.le _)
    _ = _ := by
      rw [show (-11 / 10 : ℝ) = -(11 / 10 : ℝ) by norm_num, Real.rpow_neg ht0.le]
      field_simp [hw.ne', (Real.rpow_pos_of_pos ht0 (11 / 10 : ℝ)).ne']

private lemma kernel_upper {a t x : ℝ} (ha : 4 ≤ a) (hat : a ≤ t)
    (htx : t < x) (hx : x = endpoint a) :
    kernel t x ≤ x ^ (-11 / 10 : ℝ) * (a / x) ^ (9 / 10 : ℝ) *
      (1 + (4 / 5 : ℝ) * a ^ (-1 / 5 : ℝ)) * (t - a) := by
  have ha0 : 0 < a := by linarith
  have ht0 : 0 < t := ha0.trans_le hat
  have hx0 : 0 < x := ht0.trans htx
  have htb : t ≤ endpoint t := le_add_of_nonneg_right (Real.rpow_nonneg ht0.le _)
  have hb0 : 0 < endpoint t := ht0.trans_le htb
  have hxb : x ≤ endpoint t := by
    rw [hx]
    exact endpoint_strictMonoOn.monotoneOn (by simpa using (show 1 ≤ a by linarith))
      (by simpa using (show 1 ≤ t by linarith)) hat
  have hw := weight_pos (by linarith : 1 < t)
  have hden := mul_pos hw (Real.rpow_pos_of_pos ht0 (11 / 10 : ℝ))
  have hp := price_drop_sharp (ha.trans hat) htx.le hxb
  have hn : kernel t x ≤ (t ^ (9 / 10 : ℝ) / endpoint t) / x * (endpoint t - x) := by
    rw [kernel, ite_eq_left ⟨htx, hxb⟩]
    apply (div_le_iff₀ hden).2
    calc
      _ ≤ (t ^ 2 * weight t) * ((endpoint t - x) / (x * endpoint t)) := hp
      _ = _ := by
        have hs' : t ^ 2 = t ^ (9 / 10 : ℝ) * t ^ (11 / 10 : ℝ) := by
          rw [← Real.rpow_add ht0]
          norm_num
        rw [hs']
        field_simp [hx0.ne', hb0.ne']
  have hgap : 0 ≤ endpoint t - x := sub_nonneg.mpr hxb
  have hta0 : 0 ≤ t - a := sub_nonneg.mpr hat
  have hsource := source_factor_antitone (by linarith : 1 ≤ a) hat
  rw [← hx] at hsource
  have hb := (endpoint_secants ha0 hat htx.le).2
  rw [← hx] at hb
  have hcoeff : (a ^ (9 / 10 : ℝ) / x) / x =
      x ^ (-11 / 10 : ℝ) * (a / x) ^ (9 / 10 : ℝ) := by
    rw [Real.div_rpow ha0.le hx0.le]
    have hxp : x ^ (-11 / 10 : ℝ) = x ^ (9 / 10 : ℝ) / x ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_sub hx0]
      norm_num
    rw [hxp]
    field_simp [(Real.rpow_pos_of_pos hx0 (9 / 10 : ℝ)).ne', hx0.ne']
  calc
    _ ≤ (t ^ (9 / 10 : ℝ) / endpoint t) / x * (endpoint t - x) := hn
    _ ≤ (a ^ (9 / 10 : ℝ) / x) / x * (endpoint t - x) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hsource hx0.le) hgap
    _ ≤ (a ^ (9 / 10 : ℝ) / x) / x *
        ((1 + (4 / 5 : ℝ) * a ^ (-1 / 5 : ℝ)) * (t - a)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [hcoeff]; ring

private lemma full_band_integral {a ell R x : ℝ} (ha : 4 ≤ a) (hell : 4 ≤ ell)
    (hla : ell ≤ a) (hx : x = endpoint a) (hxR : x ≤ R) :
    windowMass ell R x = ∫ t in a..x, kernel t x := by
  have ha0 : 0 < a := by linarith
  have hax : a ≤ x := by
    rw [hx]
    exact le_add_of_nonneg_right (Real.rpow_nonneg ha0.le _)
  have hsub : Icc a x ⊆ Icc ell R := Icc_subset_Icc hla hxR
  have heq : windowMass ell R x = ∫ t in Icc a x, kernel t x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc hsub
    intro t ht
    by_cases hxt : x ≤ t
    · simp [kernel, not_lt.mpr hxt]
    · have hta : t < a := by
        by_contra h
        exact ht.2 ⟨not_lt.mp h, (not_le.mp hxt).le⟩
      have hB : endpoint t < x := by
        rw [hx]
        exact endpoint_strictMonoOn (by simpa using (show 1 ≤ t by linarith [ht.1.1]))
          (by simpa using (show 1 ≤ a by linarith)) hta
      simp [kernel, not_le.mpr hB]
  rw [heq, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hax]

private lemma source_triangle (a x C : ℝ) :
    (∫ t in a..x, C * (t - a)) = C * (x - a) ^ 2 / 2 := by
  have hi : IntervalIntegrable (fun t : ℝ => C * (x - t)) volume a x := by
    apply Continuous.intervalIntegrable
    fun_prop
  calc
    _ = ∫ t in a..x, C * (x - a) - C * (x - t) := by
      apply intervalIntegral.integral_congr
      intro t _
      ring
    _ = (x - a) * (C * (x - a)) - C * (x - a) ^ 2 / 2 := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hi, triangle_integral]
      simp only [intervalIntegral.integral_const, smul_eq_mul]
    _ = _ := by ring

/-- The complete reference interval contains exactly the active band a<t<x,
where x=b(a). The lower triangle is compared only off the strict diagonal.
This is a normalizer estimate in t, not the fixed-t moment in x. -/
theorem original_full_band_normalizer {a ell R x : ℝ}
    (ha : 4 ≤ a) (hell : 4 ≤ ell) (hla : ell ≤ a)
    (hx : x = endpoint a) (hxR : x ≤ R) :
    0 < windowMass ell R x ∧
    x ^ (1 / 2 : ℝ) / 2 * (a / x) ^ (28 / 5 : ℝ) *
        (1 + (4 / 5 : ℝ) * x ^ (-1 / 5 : ℝ)) ≤ windowMass ell R x ∧
    windowMass ell R x ≤ x ^ (1 / 2 : ℝ) / 2 * (a / x) ^ (5 / 2 : ℝ) *
        (1 + (4 / 5 : ℝ) * a ^ (-1 / 5 : ℝ)) ∧
    x ^ (1 / 2 : ℝ) / 2 * (a / x) ^ (5 / 2 : ℝ) *
        (1 + (4 / 5 : ℝ) * a ^ (-1 / 5 : ℝ)) < x ^ (1 / 2 : ℝ) / 2 ∧
    |windowMass ell R x - x ^ (1 / 2 : ℝ) / 2| ≤
        (14 / 5 : ℝ) * a ^ (-1 / 5 : ℝ) * x ^ (1 / 2 : ℝ) := by
  have ha0 : 0 < a := by linarith
  have hax : a < x := by
    rw [hx]
    exact lt_add_of_pos_right a (Real.rpow_pos_of_pos ha0 _)
  have hx0 : 0 < x := ha0.trans hax
  let q : ℝ := a / x
  let δ : ℝ := a ^ (-1 / 5 : ℝ)
  let A : ℝ := x ^ (1 / 2 : ℝ) / 2
  let L : ℝ := x ^ (-11 / 10 : ℝ) * q ^ 4 *
    (1 + (4 / 5 : ℝ) * x ^ (-1 / 5 : ℝ))
  let U : ℝ := x ^ (-11 / 10 : ℝ) * q ^ (9 / 10 : ℝ) *
    (1 + (4 / 5 : ℝ) * δ)
  have hq : 0 < q := div_pos ha0 hx0
  have hδ : 0 < δ := Real.rpow_pos_of_pos ha0 _
  have hA : 0 < A := by dsimp [A]; positivity
  have hqeq : q = (1 + δ)⁻¹ := by
    dsimp [q, δ]
    rw [hx, endpoint_factor ha0]
    field_simp [ha0.ne']
  have hiK : IntervalIntegrable (fun t => kernel t x) volume a x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hax.le).2 (kernel_integrableOn ha)
  have hiL : IntervalIntegrable (fun t => L * (t - a)) volume a x := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hiU : IntervalIntegrable (fun t => U * (t - a)) volume a x := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hlow := intervalIntegral.integral_mono_on_of_le_Ioo hax.le hiL hiK
    (fun t ht => kernel_lower ha ht.1.le ht.2 hx)
  have hupp := intervalIntegral.integral_mono_on_of_le_Ioo hax.le hiK hiU
    (fun t ht => kernel_upper ha ht.1.le ht.2 hx)
  rw [source_triangle] at hlow hupp
  rw [← full_band_integral ha hell hla hx hxR] at hlow hupp
  have hscale : x ^ (-11 / 10 : ℝ) * (x - a) ^ 2 =
      x ^ (1 / 2 : ℝ) * q ^ (8 / 5 : ℝ) := by
    have hH : x - a = width a := by rw [hx]; simp [endpoint]
    have hH2 : width a ^ 2 = a ^ (8 / 5 : ℝ) := by
      unfold width
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha0.le]
      norm_num
    have hxp : x ^ (-11 / 10 : ℝ) = x ^ (1 / 2 : ℝ) / x ^ (8 / 5 : ℝ) := by
      rw [← Real.rpow_sub hx0]
      norm_num
    rw [hH, hH2, hxp]
    dsimp [q]
    rw [Real.div_rpow ha0.le hx0.le]
    ring
  have hqL : q ^ (8 / 5 : ℝ) * q ^ 4 = q ^ (28 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hq]
    norm_num
  have hqU : q ^ (8 / 5 : ℝ) * q ^ (9 / 10 : ℝ) = q ^ (5 / 2 : ℝ) := by
    rw [← Real.rpow_add hq]
    norm_num
  have hL : L * (x - a) ^ 2 / 2 =
      A * q ^ (28 / 5 : ℝ) * (1 + (4 / 5 : ℝ) * x ^ (-1 / 5 : ℝ)) := by
    calc
      _ = (x ^ (-11 / 10 : ℝ) * (x - a) ^ 2) / 2 * q ^ 4 *
          (1 + (4 / 5 : ℝ) * x ^ (-1 / 5 : ℝ)) := by dsimp [L]; ring
      _ = A * (q ^ (8 / 5 : ℝ) * q ^ 4) *
          (1 + (4 / 5 : ℝ) * x ^ (-1 / 5 : ℝ)) := by rw [hscale]; dsimp [A]; ring
      _ = _ := by rw [hqL]
  have hU : U * (x - a) ^ 2 / 2 =
      A * q ^ (5 / 2 : ℝ) * (1 + (4 / 5 : ℝ) * δ) := by
    calc
      _ = (x ^ (-11 / 10 : ℝ) * (x - a) ^ 2) / 2 * q ^ (9 / 10 : ℝ) *
          (1 + (4 / 5 : ℝ) * δ) := by dsimp [U]; ring
      _ = A * (q ^ (8 / 5 : ℝ) * q ^ (9 / 10 : ℝ)) *
          (1 + (4 / 5 : ℝ) * δ) := by rw [hscale]; dsimp [A]; ring
      _ = _ := by rw [hqU]
  rw [hL] at hlow
  rw [hU] at hupp
  have hstrict : A * q ^ (5 / 2 : ℝ) * (1 + (4 / 5 : ℝ) * δ) < A := by
    have hlin : 1 + (4 / 5 : ℝ) * δ < (1 + δ) ^ (5 / 2 : ℝ) := by
      calc
        _ < 1 + δ := by linarith
        _ ≤ (1 + δ) ^ (5 / 2 : ℝ) := by
          simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
            (show 1 ≤ 1 + δ by linarith) (by norm_num : (1 : ℝ) ≤ 5 / 2)
    have hfac : q ^ (5 / 2 : ℝ) * (1 + (4 / 5 : ℝ) * δ) < 1 := by
      rw [hqeq, Real.inv_rpow (by positivity)]
      have he : ((1 + δ) ^ (5 / 2 : ℝ))⁻¹ * (1 + (4 / 5 : ℝ) * δ) =
          (1 + (4 / 5 : ℝ) * δ) / (1 + δ) ^ (5 / 2 : ℝ) := by ring
      rw [he]
      exact (div_lt_one (by positivity)).2 hlin
    simpa only [mul_assoc, mul_one] using mul_lt_mul_of_pos_left hfac hA
  have hpositive : 0 < windowMass ell R x :=
    (show 0 < A * q ^ (28 / 5 : ℝ) *
      (1 + (4 / 5 : ℝ) * x ^ (-1 / 5 : ℝ)) by positivity).trans_le hlow
  have hcoarse : A * q ^ (28 / 5 : ℝ) ≤ windowMass ell R x := by
    calc
      _ ≤ A * q ^ (28 / 5 : ℝ) *
          (1 + (4 / 5 : ℝ) * x ^ (-1 / 5 : ℝ)) := by
        have he : 0 ≤ (4 / 5 : ℝ) * x ^ (-1 / 5 : ℝ) := by positivity
        nlinarith [mul_nonneg (by positivity : 0 ≤ A * q ^ (28 / 5 : ℝ)) he]
      _ ≤ _ := hlow
  have hqneg : q ^ (28 / 5 : ℝ) = (1 + δ) ^ (-(28 / 5 : ℝ)) := by
    rw [hqeq, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity)]
  have hfirst := mul_le_mul_of_nonneg_left
    (negative_power_lower hδ.le (by norm_num : (0 : ℝ) ≤ 28 / 5)) hA.le
  rw [← hqneg] at hfirst
  have herr : |windowMass ell R x - A| ≤ (14 / 5 : ℝ) * δ * x ^ (1 / 2 : ℝ) := by
    rw [abs_of_nonpos (sub_nonpos.mpr (hupp.trans hstrict.le))]
    have hpaid := hfirst.trans hcoarse
    dsimp [A] at hpaid ⊢
    nlinarith only [hpaid]
  exact ⟨hpositive, hlow, hupp, hstrict, herr⟩

end D5.S3.Arith.Robin.OriginalFullBandNormalizer

#print axioms D5.S3.Arith.Robin.OriginalFullBandNormalizer.original_full_band_normalizer
