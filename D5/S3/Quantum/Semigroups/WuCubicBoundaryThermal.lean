import D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
import D5.S3.Quantum.Semigroups.WuCubicThermalDerivatives
import OmegaBuild.Commands

/-! Thermal pure curvature of the fixed-frame cubic deficit. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Matrix Topology

namespace D5.S3.Quantum.Semigroups.WuCubicBoundaryThermal

open WuRepeatedMiddleCubic (weight imbalance alpha)
open private c e gamma h bias gibbsLow gibbsHigh row_weight col_weight from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private cubic levelsAt totalAt source_centered_at from
  D5.S3.Quantum.Semigroups.WuCubicSignedTransfer
open WuCubicAngularCertificate (physicalFrame normalizedDeficit thermalCenter endCharge)
open private physicalFrame_columns physicalFrame_rows physicalFrame_charge from
  D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
open WuCubicDirectedOccupationCap (Mat frameVector emptyProbability fullProbability)
open private row_mass from D5.S3.Quantum.Semigroups.WuCubicRankTwoCut

private def logMean (s : ℝ) : ℝ :=
  (1 / 2 * Real.log ((1 + s) / (1 - s))) / s

private def logMeanSlope (s : ℝ) : ℝ :=
  ((1 - s ^ 2)⁻¹ - logMean s) / s

private theorem logMean_hasDerivAt {s : ℝ} (hs : 0 < s) (hhi : s < 1) :
    HasDerivAt logMean (logMeanSlope s) s := by
  have hp : 0 < 1 - s ^ 2 := by nlinarith [mul_pos hs (sub_pos.mpr hhi)]
  have hl := Real.hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range 0
    (show -1 < s by linarith) hhi
  simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero] at hl
  refine (hl.div (hasDerivAt_id' s) hs.ne').congr_deriv ?_
  change ((1 / (1 - s ^ 2)) * s - (1 / 2 * Real.log ((1 + s) / (1 - s))) * 1) /
      s ^ 2 = logMeanSlope s
  unfold logMeanSlope logMean
  field_simp [hs.ne', hp.ne']

private def logMeanCurvature (s : ℝ) : ℝ :=
  2 / (1 - s ^ 2) ^ 2 - 2 * (logMeanSlope s / s)

private theorem logMeanSlope_hasDerivAt {s : ℝ} (hs : 0 < s) (hhi : s < 1) :
    HasDerivAt logMeanSlope (logMeanCurvature s) s := by
  have hp : 0 < 1 - s ^ 2 := by nlinarith [mul_pos hs (sub_pos.mpr hhi)]
  have hd := ((hasDerivAt_pow 2 s).const_sub 1).inv hp.ne'
  refine ((hd.sub (logMean_hasDerivAt hs hhi)).div (hasDerivAt_id' s) hs.ne').congr_deriv ?_
  simp only [logMeanSlope, logMeanCurvature, Pi.sub_apply, Pi.inv_apply, Nat.cast_ofNat,
    Nat.reduceSub, pow_one]
  field_simp [hs.ne', hp.ne']
  ring

private theorem logMean_bounds {s : ℝ} (hs : 0 < s) (hhi : s ≤ 1 / 10) :
    (1 ≤ logMean s ∧ logMean s ≤ 11 / 10) ∧
    (0 ≤ logMeanSlope s ∧ logMeanSlope s ≤ 1 / 8) ∧
    (0 ≤ logMeanCurvature s ∧ logMeanCurvature s ≤ 9 / 4) := by
  have hs1 : s < 1 := by linarith
  have hs2 : s ^ 2 ≤ (1 / 10 : ℝ) ^ 2 := pow_le_pow_left₀ hs.le hhi 2
  have hd : (99 / 100 : ℝ) ≤ 1 - s ^ 2 := by linarith
  have hp : 0 < 1 - s ^ 2 := by linarith
  have hl := Real.sum_range_le_log_div hs.le hs1 1
  have hu := Real.log_div_le_sum_range_add hs.le hs1 1
  norm_num [Finset.sum_range_succ] at hl hu
  have hg₀ : 1 ≤ logMean s := (le_div_iff₀ hs).2 (by simpa using hl)
  have hg₁ : logMean s ≤ (1 - s ^ 2)⁻¹ := by
    refine (div_le_iff₀ hs).2 (hu.trans_eq ?_)
    field_simp [hp.ne']
    ring
  have hInv : (1 - s ^ 2)⁻¹ ≤ 11 / 10 := by
    rw [inv_eq_one_div, div_le_iff₀ hp]
    linarith
  have hSlope₀ : 0 ≤ logMeanSlope s := div_nonneg (sub_nonneg.mpr hg₁) hs.le
  have hSlope₁ : logMeanSlope s ≤ s / (1 - s ^ 2) := by
    apply (div_le_iff₀ hs).2
    calc
      _ ≤ (1 - s ^ 2)⁻¹ - 1 := sub_le_sub_left hg₀ _
      _ = _ := by field_simp [hp.ne']; ring
  have hSlope₂ : s / (1 - s ^ 2) ≤ 1 / 8 := by
    rw [div_le_iff₀ hp]
    linarith
  have hRatio : logMeanSlope s / s ≤ 1 / (1 - s ^ 2) := by
    refine (div_le_iff₀ hs).2 (hSlope₁.trans_eq ?_)
    ring
  have hSqLower : (99 / 100 : ℝ) ^ 2 ≤ (1 - s ^ 2) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hd 2
  have hSqUpper : (1 - s ^ 2) ^ 2 ≤ 1 - s ^ 2 := by
    nlinarith only [mul_nonneg hp.le (sq_nonneg s)]
  refine ⟨⟨hg₀, hg₁.trans hInv⟩, ⟨hSlope₀, hSlope₁.trans hSlope₂⟩, ?_, ?_⟩
  · have H : 2 / (1 - s ^ 2) ≤ 2 / (1 - s ^ 2) ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hp) hSqUpper
    unfold logMeanCurvature
    linarith [show 2 / (1 - s ^ 2) = 2 * (1 / (1 - s ^ 2)) by ring]
  · have H : 2 / (1 - s ^ 2) ^ 2 ≤ 9 / 4 := by
      rw [div_le_iff₀ (sq_pos_of_pos hp)]
      linarith
    unfold logMeanCurvature
    linarith [div_nonneg hSlope₀ hs.le]

private def alphaDen (s : ℝ) : ℝ := (1 + s ^ 2 / 3) * logMean s

private def alphaDenSlope (s : ℝ) : ℝ :=
  (2 * s / 3) * logMean s + (1 + s ^ 2 / 3) * logMeanSlope s

private def alphaDenCurvature (s : ℝ) : ℝ :=
  (2 / 3) * logMean s + (4 * s / 3) * logMeanSlope s +
    (1 + s ^ 2 / 3) * logMeanCurvature s

private theorem alphaDen_hasDerivAt {s : ℝ} (hs : 0 < s) (hhi : s < 1) :
    HasDerivAt alphaDen (alphaDenSlope s) s := by
  have hp := (((hasDerivAt_pow 2 s).div_const 3).const_add 1)
  refine (hp.fun_mul (logMean_hasDerivAt hs hhi)).congr_deriv ?_
  unfold alphaDenSlope
  norm_num

private theorem alphaDenSlope_hasDerivAt {s : ℝ} (hs : 0 < s) (hhi : s < 1) :
    HasDerivAt alphaDenSlope (alphaDenCurvature s) s := by
  have hf := logMean_hasDerivAt hs hhi
  have hq := (((hasDerivAt_id' s).const_mul (2 : ℝ)).div_const 3).fun_mul hf
  have hp := (((hasDerivAt_pow 2 s).div_const 3).const_add 1).fun_mul
    (logMeanSlope_hasDerivAt hs hhi)
  refine (hq.fun_add hp).congr_deriv ?_
  unfold alphaDenCurvature
  norm_num
  ring

private theorem alphaDen_bounds {s : ℝ} (hs : 0 < s) (hhi : s ≤ 1 / 10) :
    1 ≤ alphaDen s ∧
    (0 ≤ alphaDenSlope s ∧ alphaDenSlope s ≤ 1 / 4) ∧
    (0 ≤ alphaDenCurvature s ∧ alphaDenCurvature s ≤ 13 / 4) := by
  obtain ⟨⟨hg₀, hg₁⟩, ⟨hp₀, hp₁⟩, ⟨hq₀, hq₁⟩⟩ := logMean_bounds hs hhi
  have hpoly₀ : 1 ≤ 1 + s ^ 2 / 3 := by linarith [sq_nonneg s]
  have hpoly₁ : 1 + s ^ 2 / 3 ≤ 101 / 100 := by
    linarith [pow_le_pow_left₀ hs.le hhi 2]
  have hbase : 1 ≤ alphaDen s := by
    simpa [alphaDen] using mul_le_mul hpoly₀ hg₀ (by norm_num) (by positivity)
  have hg : 0 ≤ logMean s := zero_le_one.trans hg₀
  unfold alphaDenSlope alphaDenCurvature
  refine ⟨hbase, ⟨by positivity, ?_⟩, ⟨by positivity, ?_⟩⟩
  · have H₁ := mul_le_mul (show 2 * s / 3 ≤ 1 / 15 by linarith) hg₁ hg (by norm_num)
    have H₂ := mul_le_mul hpoly₁ hp₁ hp₀ (by norm_num)
    linarith
  · have H₁ := mul_le_mul_of_nonneg_left hg₁ (by norm_num : (0 : ℝ) ≤ 2 / 3)
    have H₂ := mul_le_mul (show 4 * s / 3 ≤ 2 / 15 by linarith) hp₁ hp₀ (by norm_num)
    have H₃ := mul_le_mul hpoly₁ hq₁ hq₀ (by norm_num)
    linarith

private def logCoordinate (r : ℝ) : ℝ := (r - 1) / (r + 1)

private theorem logCoordinate_hasDerivAt {r : ℝ} (hr : 1 < r) :
    HasDerivAt logCoordinate (2 / (r + 1) ^ 2) r := by
  have hp : 0 < r + 1 := by linarith
  refine (((hasDerivAt_id' r).sub_const 1).div ((hasDerivAt_id' r).add_const 1)
    hp.ne').congr_deriv ?_
  apply (div_eq_div_iff (by positivity) (by positivity)).2
  ring

private theorem logCoordinateSlope_hasDerivAt {r : ℝ} (hr : 1 < r) :
    HasDerivAt (fun y : ℝ => 2 / (y + 1) ^ 2) (-4 / (r + 1) ^ 3) r := by
  have hp : 0 < r + 1 := by linarith
  refine ((hasDerivAt_const r (2 : ℝ)).div (((hasDerivAt_id' r).add_const 1).fun_pow 2)
    (pow_ne_zero 2 hp.ne')).congr_deriv ?_
  norm_num
  field_simp [hp.ne']
  ring

private theorem logCoordinate_mem {r : ℝ} (hr : 1 < r) :
    0 < logCoordinate r ∧ logCoordinate r < 1 := by
  have hp : 0 < r + 1 := by linarith
  exact ⟨div_pos (sub_pos.mpr hr) hp, (div_lt_iff₀ hp).2 (by linarith)⟩

private theorem alphaDen_pos {s : ℝ} (hs : 0 < s) (hhi : s < 1) :
    0 < alphaDen s := by
  have H := Real.sum_range_le_log_div hs.le hhi 1
  norm_num [Finset.sum_range_succ] at H
  unfold alphaDen logMean
  exact mul_pos (by positivity) (div_pos (hs.trans_le H) hs)

private theorem alpha_eq_logCoordinate {r : ℝ} (hr : 1 < r) :
    alpha r = (1 / 2) / alphaDen (logCoordinate r) := by
  have hp : 0 < r + 1 := by linarith
  have hm := logCoordinate_mem hr
  have hratio : (1 + logCoordinate r) / (1 - logCoordinate r) = r := by
    apply (div_eq_iff (sub_pos.mpr hm.2).ne').2
    unfold logCoordinate
    field_simp [hp.ne']
    ring
  rw [alpha, ite_eq_right hr.ne', alphaDen, logMean, hratio]
  have hlog := Real.log_pos hr
  have hquad : 0 < r ^ 2 + r + 1 := by positivity
  have hs := hm.1.ne'
  unfold logCoordinate at hs ⊢
  field_simp [hp.ne', (sub_pos.mpr hr).ne', hlog.ne', hquad.ne', hs]
  ring

private theorem alpha_hasDerivAt {r : ℝ} (hr : 1 < r) :
    HasDerivAt alpha
      (-((1 / 2) * (alphaDenSlope (logCoordinate r) * (2 / (r + 1) ^ 2))) /
        alphaDen (logCoordinate r) ^ 2) r := by
  obtain ⟨hs, ht⟩ := logCoordinate_mem hr
  have hd := (alphaDen_hasDerivAt hs ht).comp r (logCoordinate_hasDerivAt hr)
  refine (((hasDerivAt_const r (1 / 2 : ℝ)).div hd (alphaDen_pos hs ht).ne').congr_deriv
    ?_).congr_of_eventuallyEq ?_
  · simp only [zero_mul, zero_sub, Function.comp_apply]
  · filter_upwards [lt_mem_nhds hr] with y hy
    exact alpha_eq_logCoordinate hy

private theorem alpha_second_hasDerivAt {r : ℝ} (hr : 1 < r) :
    let s := logCoordinate r
    let v := 2 / (r + 1) ^ 2
    let a := -4 / (r + 1) ^ 3
    HasDerivAt (deriv alpha)
      (((alphaDenSlope s * v) ^ 2) / alphaDen s ^ 3 -
        ((alphaDenCurvature s * v ^ 2 + alphaDenSlope s * a) / 2) / alphaDen s ^ 2) r := by
  dsimp only
  obtain ⟨hs, ht⟩ := logCoordinate_mem hr
  have hcoord := logCoordinate_hasDerivAt hr
  have hden := (alphaDen_hasDerivAt hs ht).comp r hcoord
  have hnum := (((alphaDenSlope_hasDerivAt hs ht).comp r hcoord).fun_mul
    (logCoordinateSlope_hasDerivAt hr)).const_mul (-(1 / 2) : ℝ)
  refine ((hnum.div (hden.fun_pow 2) (pow_ne_zero 2 (alphaDen_pos hs ht).ne')).congr_deriv
    ?_).congr_of_eventuallyEq ?_
  · simp only [Function.comp_apply, Nat.reduceSub, Nat.cast_ofNat, pow_one]
    have hd := (alphaDen_pos hs ht).ne'
    have hp : r + 1 ≠ 0 := by linarith
    field_simp [hd, hp]
    ring
  · filter_upwards [lt_mem_nhds hr] with y hy
    rw [(alpha_hasDerivAt hy).deriv]
    simp only [Function.comp_apply, Pi.div_apply]
    ring

/-- The actual logarithmic coefficient satisfies the thermal replay's bound. -/
theorem alpha_second_abs_le {r : ℝ} (hr : 1 < r) (hhi : r ≤ 6 / 5) :
    |deriv (deriv alpha) r| ≤ 1 := by
  let s := logCoordinate r
  let v : ℝ := 2 / (r + 1) ^ 2
  let a : ℝ := -4 / (r + 1) ^ 3
  have hp : 0 < r + 1 := by linarith
  have hp₂ : (2 : ℝ) ^ 2 ≤ (r + 1) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
  have hp₃ : (2 : ℝ) ^ 3 ≤ (r + 1) ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
  have hv₀ : 0 ≤ v := by positivity
  have hv₁ : v ≤ 1 / 2 := (div_le_iff₀ (by positivity)).2 (by linarith)
  have hv₂ : v ^ 2 ≤ 1 / 4 := by
    linarith [pow_le_pow_left₀ hv₀ hv₁ 2]
  have ha : |a| ≤ 1 / 2 := by
    dsimp [a]
    rw [abs_div, abs_of_pos (pow_pos hp 3), abs_neg]
    norm_num
    rw [div_le_iff₀ (pow_pos hp 3)]
    linarith
  have hs : s ≤ 1 / 10 := (div_le_iff₀ hp).2 (by linarith)
  obtain ⟨hd, ⟨hf₀, hf₁⟩, ⟨hg₀, hg₁⟩⟩ := alphaDen_bounds (logCoordinate_mem hr).1 hs
  have hd₀ : 0 < alphaDen s := zero_lt_one.trans_le hd
  have hd₂ : 1 ≤ alphaDen s ^ 2 := by simpa using pow_le_pow_left₀ zero_le_one hd 2
  have hd₃ : 1 ≤ alphaDen s ^ 3 := by simpa using pow_le_pow_left₀ zero_le_one hd 3
  have hprod : alphaDenSlope s * v ≤ 1 / 4 * (1 / 2) :=
    mul_le_mul hf₁ hv₁ hv₀ (by norm_num)
  have hsq : (alphaDenSlope s * v) ^ 2 ≤ 1 / 64 := by
    convert pow_le_pow_left₀ (mul_nonneg hf₀ hv₀) hprod 2 using 1
    norm_num
  have hfirst : |(alphaDenSlope s * v) ^ 2 / alphaDen s ^ 3| ≤ 1 / 64 := by
    rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (by positivity)), div_le_iff₀ (by positivity)]
    linarith
  have hsecond : |((alphaDenCurvature s * v ^ 2 + alphaDenSlope s * a) / 2) /
      alphaDen s ^ 2| ≤ 15 / 32 := by
    have H₁ := mul_le_mul hg₁ hv₂ (sq_nonneg v) (by norm_num)
    have H₂ := mul_le_mul hf₁ ha (abs_nonneg a) (by norm_num)
    have H := abs_add_le (alphaDenCurvature s * v ^ 2) (alphaDenSlope s * a)
    rw [abs_of_nonneg (mul_nonneg hg₀ (sq_nonneg v)), abs_mul, abs_of_nonneg hf₀] at H
    rw [abs_div, abs_div, abs_of_pos (pow_pos hd₀ 2)]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [div_le_iff₀ (pow_pos hd₀ 2)]
    linarith
  rw [(alpha_second_hasDerivAt hr).deriv]
  change |(alphaDenSlope s * v) ^ 2 / alphaDen s ^ 3 -
    ((alphaDenCurvature s * v ^ 2 + alphaDenSlope s * a) / 2) / alphaDen s ^ 2| ≤ 1
  exact (abs_sub _ _).trans (by linarith)

private def biasDen (r : ℝ) : ℝ := (1 + r ^ 3) * (r ^ 2 + r + 1)

private theorem biasDen_hasDerivAt (r : ℝ) :
    HasDerivAt biasDen (3 * r ^ 2 * (r ^ 2 + r + 1) + (1 + r ^ 3) * (2 * r + 1)) r := by
  have hp := (hasDerivAt_pow 3 r).const_add 1
  have hq := ((hasDerivAt_pow 2 r).add (hasDerivAt_id' r)).add_const 1
  refine (hp.fun_mul hq).congr_deriv ?_
  simp only [Pi.add_apply, Nat.reduceSub, Nat.cast_ofNat, pow_one]

private theorem bias_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt bias
      (-3 * (r ^ 8 + 6*r ^ 7 - 7*r ^ 6 - 12*r ^ 5 - 12*r ^ 4 - 12*r ^ 3 -
        7*r ^ 2 + 6*r + 1) / (2 * biasDen r ^ 2)) r := by
  have hP : 0 < biasDen r := by unfold biasDen; positivity
  have h₁ := (hasDerivAt_pow 4 r).add ((hasDerivAt_pow 3 r).const_mul (3 : ℝ))
  have h₂ := ((hasDerivAt_pow 2 r).const_mul (3 : ℝ)).add (hasDerivAt_id' r)
  have hn := (h₁.sub h₂).const_mul (3 : ℝ)
  have hd := (biasDen_hasDerivAt r).const_mul (2 : ℝ)
  refine ((hn.div hd (mul_ne_zero (by norm_num) hP.ne')).congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [biasDen, Pi.add_apply, Pi.sub_apply, Nat.reduceSub, Nat.cast_ofNat, pow_one]
    apply (div_eq_div_iff (by positivity) (by positivity)).2
    ring
  · filter_upwards [lt_mem_nhds hr] with y hy
    have hP : 0 < (1 + y ^ 3) * (y ^ 2 + y + 1) := by positivity
    change 2 * gamma y * y * (y - 1) * (y ^ 2 + 4*y + 1) / (3 * (y ^ 2 + y + 1)) =
      3 * (y ^ 4 + 3*y ^ 3 - (3*y ^ 2 + y)) / (2 * biasDen y)
    unfold gamma biasDen
    field_simp
    ring

private theorem bias_second_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt (deriv bias)
      (3 * (r ^ 12 + 9*r ^ 11 - 12*r ^ 10 - 42*r ^ 9 - 66*r ^ 8 - 84*r ^ 7 -
        71*r ^ 6 + 27*r ^ 5 + 48*r ^ 4 + 42*r ^ 3 + 30*r ^ 2 + 12*r - 2) /
        biasDen r ^ 3) r := by
  have hp : 0 < biasDen r := by unfold biasDen; positivity
  have h₁ := (hasDerivAt_pow 8 r).add ((hasDerivAt_pow 7 r).const_mul (6 : ℝ))
  have h₂ := ((hasDerivAt_pow 6 r).const_mul (7 : ℝ)).add
    ((hasDerivAt_pow 5 r).const_mul (12 : ℝ))
  have h₃ := ((hasDerivAt_pow 4 r).const_mul (12 : ℝ)).add
    ((hasDerivAt_pow 3 r).const_mul (12 : ℝ))
  have h₄ := (hasDerivAt_pow 2 r).const_mul (7 : ℝ)
  have hn := (((((h₁.sub h₂).sub h₃).sub h₄).add
    ((hasDerivAt_id' r).const_mul (6 : ℝ))).add_const 1).const_mul (-3 : ℝ)
  have hd := ((biasDen_hasDerivAt r).fun_pow 2).const_mul (2 : ℝ)
  refine ((hn.div hd (mul_ne_zero (by norm_num) (pow_ne_zero 2 hp.ne'))).congr_deriv
    ?_).congr_of_eventuallyEq ?_
  · simp only [Pi.add_apply, Pi.sub_apply, Nat.reduceSub, Nat.cast_ofNat, pow_one]
    field_simp [hp.ne']
    unfold biasDen
    ring
  · filter_upwards [lt_mem_nhds hr] with y hy
    rw [(bias_hasDerivAt hy).deriv]
    simp only [Pi.div_apply, Pi.add_apply, Pi.sub_apply]
    ring

/-- The actual signed bias satisfies the replay's absolute curvature bound. -/
theorem bias_second_abs_le {r : ℝ} (hr : 1 ≤ r) : |deriv (deriv bias) r| ≤ 18 := by
  have hr₀ := zero_lt_one.trans_le hr
  have hp : 0 < biasDen r ^ 3 := by unfold biasDen; positivity
  rw [(bias_second_hasDerivAt hr₀).deriv, abs_le]
  let t := r - 1
  have ht : 0 ≤ t := sub_nonneg.mpr hr
  have heq : r = t + 1 := by dsimp [t]; ring
  constructor
  · apply (le_div_iff₀ hp).2
    have H : 0 ≤ 18*t^15 + 324*t^14 + 2754*t^13 + 14691*t^12 + 55143*t^11 +
        154683*t^10 + 335757*t^9 + 575172*t^8 + 784674*t^7 + 852861*t^6 +
        733239*t^5 + 491697*t^4 + 251865*t^3 + 95418*t^2 + 24948*t + 3564 := by positivity
    unfold biasDen
    rw [heq]
    linear_combination H
  · apply (div_le_iff₀ hp).2
    have H : 0 ≤ 18*t^15 + 324*t^14 + 2754*t^13 + 14685*t^12 + 55017*t^11 +
        153765*t^10 + 332439*t^9 + 569196*t^8 + 783486*t^7 + 873699*t^6 +
        788589*t^5 + 568431*t^4 + 316755*t^3 + 128142*t^2 + 33372*t + 4212 := by positivity
    unfold biasDen
    rw [heq]
    linear_combination H

private theorem c_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt c (9 * (1 - r ^ 2) / (8 * (r ^ 2 - r + 1) ^ 2)) r := by
  have hp : 0 < r ^ 2 - r + 1 := by nlinarith [sq_nonneg (r - 1 / 2)]
  have hn := (hasDerivAt_id' r).const_mul (9 : ℝ)
  have hd := ((((hasDerivAt_pow 2 r).sub (hasDerivAt_id' r)).add_const 1).const_mul (8 : ℝ))
  have H := hn.div hd (mul_ne_zero (by norm_num) hp.ne')
  refine (H.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [Pi.sub_apply]
    field_simp [hp.ne']
    ring
  · filter_upwards [lt_mem_nhds hr] with y hy
    have hp : 0 < y ^ 2 - y + 1 := by nlinarith [sq_nonneg (y - 1 / 2)]
    have hq : 0 < 1 + y ^ 3 := by positivity
    change 9 / (4 * (1 + y ^ 3)) * y * (y + 1) / 2 =
      9 * y / (8 * (y ^ 2 - y + 1))
    calc
      _ = 9 * y * (y + 1) / (8 * (1 + y ^ 3)) := by
        field_simp [hq.ne']
        ring
      _ = _ := (div_eq_div_iff (by positivity) (by positivity)).2 (by ring)

/-- Exact ordinary second derivative of the actual symmetric coefficient. -/
theorem c_second_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt (deriv c) (9 * (r ^ 3 - 3 * r + 1) / (4 * (r ^ 2 - r + 1) ^ 3)) r := by
  have hp : 0 < r ^ 2 - r + 1 := by nlinarith [sq_nonneg (r - 1 / 2)]
  have hn := (((hasDerivAt_pow 2 r).const_sub 1).const_mul (9 : ℝ))
  have hd := ((((hasDerivAt_pow 2 r).sub (hasDerivAt_id' r)).add_const 1).fun_pow 2).const_mul
    (8 : ℝ)
  have H := hn.div hd (mul_ne_zero (by norm_num) (pow_ne_zero 2 hp.ne'))
  refine (H.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [Pi.sub_apply, Nat.reduceSub, pow_one, Nat.cast_ofNat]
    apply (div_eq_div_iff (by positivity) (by positivity)).2
    ring
  · filter_upwards [lt_mem_nhds hr] with y hy
    exact (c_hasDerivAt hy).deriv

theorem c_second_nonpos {r : ℝ} (hr : 1 ≤ r) (hhi : r ≤ 6 / 5) :
    deriv (deriv c) r ≤ 0 := by
  have hr₀ : 0 < r := zero_lt_one.trans_le hr
  rw [(c_second_hasDerivAt hr₀).deriv]
  have ht : 0 ≤ r - 1 := sub_nonneg.mpr hr
  have hth : r - 1 ≤ 1 / 5 := by linarith
  have ht₂ := pow_le_pow_left₀ ht hth 2
  have ht₃ := pow_le_pow_left₀ ht hth 3
  have hp : 0 < r ^ 2 - r + 1 := by nlinarith [sq_nonneg (r - 1 / 2)]
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  nlinarith only [ht₂, ht₃]

private theorem c_second_lower {r : ℝ} (hr : 1 ≤ r) : -(9 / 4 : ℝ) ≤ deriv (deriv c) r := by
  have hp : 1 ≤ r ^ 2 - r + 1 := by nlinarith [mul_nonneg (by linarith : 0 ≤ r) (sub_nonneg.mpr hr)]
  have hp₃ : (1 : ℝ) ≤ (r ^ 2 - r + 1) ^ 3 := by simpa using pow_le_pow_left₀ zero_le_one hp 3
  rw [(c_second_hasDerivAt (zero_lt_one.trans_le hr)).deriv]
  apply (le_div_iff₀ (by positivity)).2
  nlinarith only [hp₃, mul_nonneg (sq_nonneg (r - 1)) (show 0 ≤ r + 2 by linarith)]

private def thermalLog (r : ℝ) : ℝ := Real.log 4 + 3 * Real.log r - 2 * Real.log (1 + r ^ 3)

private theorem thermalLog_eq {r : ℝ} (hr : 0 < r) :
    thermalLog r = Real.log (4 * r ^ 3 / (1 + r ^ 3) ^ 2) := by
  rw [thermalLog, Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num)
    (pow_ne_zero 3 hr.ne'), Real.log_pow, Real.log_pow]
  norm_num

private theorem thermalLog_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt thermalLog (-3 * (r ^ 3 - 1) / (r * (1 + r ^ 3))) r := by
  have hp : 0 < 1 + r ^ 3 := by positivity
  have hl := ((Real.hasDerivAt_log hr.ne').const_mul (3 : ℝ)).const_add (Real.log 4)
  have hh := ((((hasDerivAt_pow 3 r).const_add 1).log hp.ne').const_mul (2 : ℝ))
  refine (hl.fun_sub hh).congr_deriv ?_
  norm_num
  field_simp [hr.ne', hp.ne']
  ring

private theorem thermalLog_second_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt (deriv thermalLog)
      (3 * (r ^ 6 - 6 * r ^ 3 - 1) / (r ^ 2 * (1 + r ^ 3) ^ 2)) r := by
  have hp : 0 < 1 + r ^ 3 := by positivity
  have hn := ((hasDerivAt_pow 3 r).sub_const 1).const_mul (-3 : ℝ)
  have hd := (hasDerivAt_id' r).fun_mul ((hasDerivAt_pow 3 r).const_add 1)
  refine ((hn.div hd (mul_ne_zero hr.ne' hp.ne')).congr_deriv ?_).congr_of_eventuallyEq ?_
  · norm_num
    apply (div_eq_div_iff (by positivity) (by positivity)).2
    ring
  · filter_upwards [lt_mem_nhds hr] with y hy
    exact (thermalLog_hasDerivAt hy).deriv

private theorem h_eq {r : ℝ} (hr : 0 < r) :
    h r = (9 / 4 - 2 * c r) + alpha r * thermalLog r := by
  have hp : 0 < 1 + r ^ 3 := by positivity
  rw [thermalLog_eq hr]
  have hg : 4 * gibbsLow r * gibbsHigh r = 4 * r ^ 3 / (1 + r ^ 3) ^ 2 := by
    unfold gibbsHigh gibbsLow
    field_simp [hp.ne']
  rw [h, hg]
  unfold c gamma
  field_simp [hp.ne']
  ring

private theorem h_hasDerivAt {r : ℝ} (hr : 1 < r) :
    HasDerivAt h
      (-2 * deriv c r + (deriv alpha r * thermalLog r + alpha r * deriv thermalLog r)) r := by
  have hr₀ : 0 < r := zero_lt_one.trans hr
  have hc := ((c_hasDerivAt hr₀).congr_deriv (c_hasDerivAt hr₀).deriv.symm).const_mul (-2 : ℝ)
  have ha := (alpha_hasDerivAt hr).congr_deriv (alpha_hasDerivAt hr).deriv.symm
  have hl := (thermalLog_hasDerivAt hr₀).congr_deriv (thermalLog_hasDerivAt hr₀).deriv.symm
  refine ((hc.const_add (9 / 4)).fun_add (ha.fun_mul hl)).congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hr] with y hy
  rw [h_eq (zero_lt_one.trans hy)]
  ring

private theorem h_second_hasDerivAt {r : ℝ} (hr : 1 < r) :
    HasDerivAt (deriv h)
      (-2 * deriv (deriv c) r +
        (deriv (deriv alpha) r * thermalLog r + 2 * deriv alpha r * deriv thermalLog r +
          alpha r * deriv (deriv thermalLog) r)) r := by
  have hr₀ : 0 < r := zero_lt_one.trans hr
  have hc := c_second_hasDerivAt hr₀
  have ha := alpha_second_hasDerivAt hr
  have hl := thermalLog_second_hasDerivAt hr₀
  have ha₁ := (alpha_hasDerivAt hr).congr_deriv (alpha_hasDerivAt hr).deriv.symm
  have hl₁ := (thermalLog_hasDerivAt hr₀).congr_deriv (thermalLog_hasDerivAt hr₀).deriv.symm
  have h₁ := (ha.congr_deriv ha.deriv.symm).fun_mul hl₁
  have h₂ := ha₁.fun_mul (hl.congr_deriv hl.deriv.symm)
  refine ((((hc.congr_deriv hc.deriv.symm).const_mul (-2 : ℝ)).fun_add
    (h₁.fun_add h₂)).congr_deriv ?_).congr_of_eventuallyEq ?_
  · ring
  · filter_upwards [lt_mem_nhds hr] with y hy
    exact (h_hasDerivAt hy).deriv

/-- Upper thermal curvature of the actual Gibbs coefficient. -/
theorem h_second_le {r : ℝ} (hr : 1 < r) (hhi : r ≤ 6 / 5) :
    deriv (deriv h) r ≤ 11 := by
  have hr₀ := zero_lt_one.trans hr
  have hr₃ : 1 ≤ r ^ 3 := by simpa using pow_le_pow_left₀ zero_le_one hr.le 3
  have hb₃ : r ^ 3 ≤ 2 := by linarith [pow_le_pow_left₀ hr₀.le hhi 3]
  have hp : 0 < 1 + r ^ 3 := by positivity
  have hl : |thermalLog r| ≤ 2 := by
    let g := 4 * r ^ 3 / (1 + r ^ 3) ^ 2
    have hg : 0 < g := by dsimp [g]; positivity
    have h₁ : g ≤ 1 := by
      apply (div_le_iff₀ (sq_pos_of_pos hp)).2
      nlinarith [sq_nonneg (r ^ 3 - 1)]
    have h₂ : g⁻¹ ≤ 3 := by
      dsimp [g]
      rw [inv_div, div_le_iff₀ (by positivity)]
      nlinarith only [mul_nonneg hp.le (show 0 ≤ 2 - r ^ 3 by linarith),
        mul_nonneg (pow_nonneg hr₀.le 3) (show 0 ≤ 2 - r ^ 3 by linarith), hr₃, hb₃]
    rw [thermalLog_eq hr₀, abs_le]
    exact ⟨by linarith [Real.one_sub_inv_le_log_of_pos hg],
      by linarith [Real.log_le_sub_one_of_pos hg]⟩
  have hl₁ : |deriv thermalLog r| ≤ 3 := by
    rw [(thermalLog_hasDerivAt hr₀).deriv, abs_div, abs_of_pos (mul_pos hr₀ hp),
      abs_mul, abs_of_nonneg (sub_nonneg.mpr hr₃), div_le_iff₀ (mul_pos hr₀ hp)]
    norm_num
    nlinarith only [mul_nonneg (sub_nonneg.mpr hr.le) hp.le]
  have hl₂ : deriv (deriv thermalLog) r ≤ 0 := by
    rw [(thermalLog_second_hasDerivAt hr₀).deriv]
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    nlinarith only [mul_nonneg (pow_nonneg hr₀.le 3) (sub_nonneg.mpr hb₃), hr₃]
  have hsp : logCoordinate r ≤ 1 / 10 := by
    apply (div_le_iff₀ (show 0 < r + 1 by linarith)).2
    linarith
  obtain ⟨hd, ⟨hf₀, hf₁⟩, _⟩ := alphaDen_bounds (logCoordinate_mem hr).1 hsp
  have hd₀ : 0 < alphaDen (logCoordinate r) := zero_lt_one.trans_le hd
  have ha₀ : 0 ≤ alpha r := by rw [alpha_eq_logCoordinate hr]; positivity
  have ha₁ : |deriv alpha r| ≤ 1 / 16 := by
    have hv : 2 / (r + 1) ^ 2 ≤ (1 / 2 : ℝ) := by
      apply (div_le_iff₀ (show 0 < (r + 1) ^ 2 by positivity)).2
      linarith [pow_le_pow_left₀ (show 0 ≤ (2 : ℝ) by norm_num)
        (show 2 ≤ r + 1 by linarith) 2]
    have hp := mul_le_mul hf₁ hv (show 0 ≤ 2 / (r + 1) ^ 2 by positivity)
      (show 0 ≤ (1 / 4 : ℝ) by norm_num)
    have hd₂ : 1 ≤ alphaDen (logCoordinate r) ^ 2 := by
      simpa using pow_le_pow_left₀ zero_le_one hd 2
    rw [(alpha_hasDerivAt hr).deriv, abs_div, abs_neg, abs_of_pos (pow_pos hd₀ 2),
      abs_of_nonneg (show 0 ≤ 1 / 2 * (alphaDenSlope (logCoordinate r) *
        (2 / (r + 1) ^ 2)) by positivity), div_le_iff₀ (pow_pos hd₀ 2)]
    linarith
  have H₁ : deriv (deriv alpha) r * thermalLog r ≤ 1 * 2 := calc
    _ ≤ |deriv (deriv alpha) r * thermalLog r| := le_abs_self _
    _ = _ * _ := abs_mul _ _
    _ ≤ _ := mul_le_mul (alpha_second_abs_le hr hhi) hl (abs_nonneg _) (by norm_num)
  have H₂ : deriv alpha r * deriv thermalLog r ≤ (1 / 16) * 3 := calc
    _ ≤ |deriv alpha r * deriv thermalLog r| := le_abs_self _
    _ = _ * _ := abs_mul _ _
    _ ≤ _ := mul_le_mul ha₁ hl₁ (abs_nonneg _) (by norm_num)
  rw [(h_second_hasDerivAt hr).deriv]
  linarith [c_second_lower hr.le, mul_nonpos_of_nonneg_of_nonpos ha₀ hl₂]

private theorem e_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt e (3 * (-r ^ 4 + 2 * r ^ 3 + 2 * r - 1) / (8 * (1 + r ^ 3) ^ 2)) r := by
  have hp : 0 < 1 + r ^ 3 := by positivity
  have hn := ((hasDerivAt_id' r).fun_mul ((hasDerivAt_id' r).sub_const 1)).const_mul (3 : ℝ)
  have hd := ((hasDerivAt_pow 3 r).const_add 1).const_mul (8 : ℝ)
  have H := hn.div hd (mul_ne_zero (by norm_num) hp.ne')
  refine (H.congr_deriv ?_).congr_of_eventuallyEq ?_
  · field_simp [hp.ne']
    ring
  · filter_upwards [lt_mem_nhds hr] with y hy
    have hp : 0 < 1 + y ^ 3 := by positivity
    dsimp [e, gamma]
    field_simp [hp.ne']
    ring

/-- Exact ordinary second derivative of the actual signed cubic coefficient. -/
theorem e_second_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt (deriv e)
      (3 * (r ^ 6 - 3 * r ^ 5 - 7 * r ^ 3 + 6 * r ^ 2 + 1) / (4 * (1 + r ^ 3) ^ 3)) r := by
  have hp : 0 < 1 + r ^ 3 := by positivity
  have hn := ((((hasDerivAt_pow 4 r).neg.add ((hasDerivAt_pow 3 r).const_mul (2 : ℝ))).add
    ((hasDerivAt_id' r).const_mul (2 : ℝ))).sub_const 1).const_mul (3 : ℝ)
  have hd := (((hasDerivAt_pow 3 r).const_add 1).fun_pow 2).const_mul (8 : ℝ)
  have H := hn.div hd (mul_ne_zero (by norm_num) (pow_ne_zero 2 hp.ne'))
  refine (H.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [Pi.add_apply, Pi.neg_apply]
    field_simp [hp.ne']
    ring
  · filter_upwards [lt_mem_nhds hr] with y hy
    exact (e_hasDerivAt hy).deriv

/-- The coefficient of the signed cubic term is bounded by one in absolute
second derivative, on the full positive-temperature side `r ≥ 1`. -/
theorem e_second_abs_le {r : ℝ} (hr : 1 ≤ r) : |deriv (deriv e) r| ≤ 1 := by
  have hr₀ : 0 < r := zero_lt_one.trans_le hr
  rw [(e_second_hasDerivAt hr₀).deriv, abs_le]
  have hp : 0 < 4 * (1 + r ^ 3) ^ 3 := by positivity
  let t := r - 1
  have ht : 0 ≤ t := sub_nonneg.mpr hr
  have heq : r = t + 1 := by dsimp [t]; ring
  constructor
  · apply (le_div_iff₀ hp).2
    have h : 0 ≤ 4*t^9 + 36*t^8 + 144*t^7 + 351*t^6 + 585*t^5 +
        684*t^4 + 537*t^3 + 270*t^2 + 90*t + 26 := by positivity
    rw [heq]
    linear_combination h
  · apply (div_le_iff₀ hp).2
    have h : 0 ≤ 4*t^9 + 36*t^8 + 144*t^7 + 345*t^6 + 567*t^5 +
        684*t^4 + 639*t^3 + 450*t^2 + 198*t + 38 := by positivity
    rw [heq]
    linear_combination h

/-- The sum of the two literal directed CAR jump weights is exactly four. -/
private theorem physical_weight_total (U : unitary Mat) :
    (∑ i, ∑ j, weight (physicalFrame U) i j) = 4 := by
  let V := physicalFrame U
  have hrow : ∀ i, (∑ j, weight V i j) = 1 + imbalance V i :=
    row_weight V (physicalFrame_columns U) (physicalFrame_rows U)
  have hcol : ∀ i, (∑ j, weight V j i) = 1 - imbalance V i :=
    col_weight V (physicalFrame_columns U) (physicalFrame_rows U)
  have hsum : (∑ i, (1 + imbalance V i)) = ∑ i, (1 - imbalance V i) := by
    simp_rw [← hrow, ← hcol]
    exact Finset.sum_comm
  change (∑ i, ∑ j, weight V i j) = 4
  simp only [hrow, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat, mul_one]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, mul_one] at hsum
  linarith

private theorem levelsAt_mem {m n q l : ℝ} (hm : l ≤ m ∧ m ≤ 1) (hn : l ≤ n ∧ n ≤ 1)
    (hq : l ≤ q ∧ q ≤ 1) (i : Fin 4) : l ≤ levelsAt m n q i ∧ levelsAt m n q i ≤ 1 := by
  have hl₁ : l ≤ 1 := hm.1.trans hm.2
  fin_cases i
  · simpa [levelsAt] using hm
  · simpa [levelsAt] using hn
  · simpa [levelsAt] using hq
  · simpa [levelsAt] using hl₁

/-- The charge contracted with the four spectral cubes in the fixed frame. -/
def spectralCharge (U : unitary Mat) (m n q : ℝ) : ℝ :=
  imbalance (physicalFrame U) 0 * m^3 + imbalance (physicalFrame U) 1 * n^3 +
    imbalance (physicalFrame U) 2 * q^3 + imbalance (physicalFrame U) 3

private theorem spectralCharge_abs_le (U : unitary Mat) {m n q l : ℝ} (hl : 0 < l)
    (hm : l ≤ m ∧ m ≤ 1) (hn : l ≤ n ∧ n ≤ 1) (hq : l ≤ q ∧ q ≤ 1) :
    |spectralCharge U m n q| ≤ 1 - l ^ 3 := by
  let x := levelsAt m n q
  let S (j : Fin 4) := ∑ i, Complex.normSq ((U : Mat) j i) * x i ^ 3
  have hS (j : Fin 4) : l ^ 3 ≤ S j ∧ S j ≤ 1 := by
    have hx (i : Fin 4) := levelsAt_mem hm hn hq i
    have heq (a : ℝ) : (∑ i, Complex.normSq ((U : Mat) j i) * a) = a := by
      rw [← Finset.sum_mul, row_mass U j, one_mul]
    constructor
    · rw [← heq (l ^ 3)]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hl.le (hx i).1 3) (Complex.normSq_nonneg _)
    · rw [← heq 1]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
        (by simpa using pow_le_pow_left₀ (hl.le.trans (hx i).1) (hx i).2 3)
        (Complex.normSq_nonneg _)
  have heq : spectralCharge U m n q = S 0 - S 3 := by
    simp only [spectralCharge, physicalFrame_charge, endCharge, emptyProbability,
      fullProbability, frameVector, S, Fin.sum_univ_four, x, levelsAt]
    norm_num
    ring
  rw [heq, abs_le]
  exact ⟨by linarith [(hS 0).1, (hS 3).2], by linarith [(hS 3).1, (hS 0).2]⟩

/-- The exact signed bias contribution in the fixed frame satisfies the replay bound. -/
theorem biasContribution_second_abs_le (U : unitary Mat) {m n q l r : ℝ}
    (hl : 0 < l) (hm : l ≤ m ∧ m ≤ 1) (hn : l ≤ n ∧ n ≤ 1)
    (hq : l ≤ q ∧ q ≤ 1) (hr : 1 ≤ r) :
    |deriv (deriv (fun y => bias y * spectralCharge U m n q)) r| ≤ 18 * (1 - l ^ 3) := by
  simp only [deriv_mul_const_field', abs_mul]
  exact mul_le_mul (bias_second_abs_le hr) (spectralCharge_abs_le U hl hm hn hq)
    (abs_nonneg _) (by norm_num)

/-- This is the literal cubic jump contribution of `source_centered_at`
used in the expansion of `normalizedDeficit`, with the spectral frame held fixed. -/
def jumpContribution (U : unitary Mat) (m n q r : ℝ) : ℝ :=
  ∑ i, ∑ j, weight (physicalFrame U) i j * cubic (c r) (e r) (levelsAt m n q i) (levelsAt m n q j)

/-- The jump contribution is precisely the one in the centered, physical
normalized deficit, with the same Gibbs mass and spectral charge terms. -/
theorem normalizedDeficit_eq_jumpContribution {r m n q : ℝ} (U : unitary Mat)
    (hr : 1 ≤ r) (hm : 0 ≤ m) (hn : 0 ≤ n) (hq : 0 ≤ q) :
    normalizedDeficit r U m n q = thermalCenter r m n q + jumpContribution U m n q r +
      bias r * (imbalance (physicalFrame U) 0 * m^3 + imbalance (physicalFrame U) 1 * n^3 +
        imbalance (physicalFrame U) 2 * q^3 + imbalance (physicalFrame U) 3) := by
  unfold normalizedDeficit
  rw [source_centered_at hr _ (physicalFrame_columns U) (physicalFrame_rows U) hm hn hq]
  rfl

private theorem jumpContribution_eq (U : unitary Mat) (m n q : ℝ) :
    jumpContribution U m n q = fun r =>
      c r * (∑ i, ∑ j, weight (physicalFrame U) i j *
        (levelsAt m n q i - levelsAt m n q j)^2 * (levelsAt m n q i + levelsAt m n q j)) +
      e r * (∑ i, ∑ j, weight (physicalFrame U) i j * (levelsAt m n q i - levelsAt m n q j)^3) := by
  funext r
  simp only [jumpContribution, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold cubic
  ring

private theorem jumpContribution_hasDerivAt (U : unitary Mat) (m n q : ℝ)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (jumpContribution U m n q) (deriv (jumpContribution U m n q) r) r := by
  rw [jumpContribution_eq]
  let V := physicalFrame U
  let x := levelsAt m n q
  let A : ℝ := ∑ i, ∑ j, weight V i j * (x i - x j)^2 * (x i + x j)
  let B : ℝ := ∑ i, ∑ j, weight V i j * (x i - x j)^3
  have H := ((c_hasDerivAt hr).mul_const A).fun_add ((e_hasDerivAt hr).mul_const B)
  exact H.congr_deriv H.deriv.symm

private theorem jumpContribution_second_hasDerivAt (U : unitary Mat) (m n q : ℝ)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (deriv (jumpContribution U m n q))
      (deriv (deriv (jumpContribution U m n q)) r) r := by
  rw [jumpContribution_eq]
  let V := physicalFrame U
  let x := levelsAt m n q
  let A : ℝ := ∑ i, ∑ j, weight V i j * (x i - x j)^2 * (x i + x j)
  let B : ℝ := ∑ i, ∑ j, weight V i j * (x i - x j)^3
  have hfirst : ∀ᶠ y in 𝓝 r, deriv (fun z => c z * A + e z * B) y =
      deriv c y * A + deriv e y * B := by
    filter_upwards [lt_mem_nhds hr] with y hy
    rw [(c_hasDerivAt hy).deriv, (e_hasDerivAt hy).deriv]
    exact (((c_hasDerivAt hy).mul_const A).fun_add ((e_hasDerivAt hy).mul_const B)).deriv
  have H := (((c_second_hasDerivAt hr).mul_const A).fun_add
    ((e_second_hasDerivAt hr).mul_const B)).congr_of_eventuallyEq hfirst
  exact H.congr_deriv H.deriv.symm

/-- The signed jump contribution obeys the replay's pure thermal bound.
No ordering of the positive levels is needed. -/
theorem jumpContribution_second_le (U : unitary Mat) {m n q l r : ℝ}
    (hl : 0 < l) (hm : l ≤ m ∧ m ≤ 1) (hn : l ≤ n ∧ n ≤ 1)
    (hq : l ≤ q ∧ q ≤ 1) (hr : 1 ≤ r) (hhi : r ≤ 6 / 5) :
    deriv (deriv (jumpContribution U m n q)) r ≤ 4 * (1 - l)^3 := by
  let V := physicalFrame U
  let x := levelsAt m n q
  let A : ℝ := ∑ i, ∑ j, weight V i j * (x i - x j)^2 * (x i + x j)
  let B : ℝ := ∑ i, ∑ j, weight V i j * (x i - x j)^3
  have hx (i : Fin 4) : l ≤ x i ∧ x i ≤ 1 := levelsAt_mem hm hn hq i
  have hw (i j : Fin 4) : 0 ≤ weight V i j := Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _
  have hA : 0 ≤ A := by
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro j _
    exact mul_nonneg (mul_nonneg (hw i j) (sq_nonneg _))
      (add_nonneg (hl.le.trans (hx i).1) (hl.le.trans (hx j).1))
  have hB : |B| ≤ 4 * (1-l)^3 := by
    have hterm (i j : Fin 4) : |weight V i j * (x i - x j)^3| ≤ weight V i j * (1-l)^3 := by
      rw [abs_mul, abs_of_nonneg (hw i j), abs_pow]
      apply mul_le_mul_of_nonneg_left _ (hw i j)
      apply pow_le_pow_left₀ (abs_nonneg _)
      rw [abs_le]
      exact ⟨by linarith [(hx i).1, (hx j).2], by linarith [(hx i).2, (hx j).1]⟩
    calc
      |B| ≤ ∑ i, |∑ j, weight V i j * (x i - x j)^3| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |weight V i j * (x i - x j)^3| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, weight V i j * (1-l)^3 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      _ = 4 * (1-l)^3 := by simp_rw [← Finset.sum_mul]; rw [physical_weight_total U]
  have hr₀ : 0 < r := zero_lt_one.trans_le hr
  have hfirst : ∀ᶠ y in 𝓝 r, deriv (jumpContribution U m n q) y =
      deriv c y * A + deriv e y * B := by
    filter_upwards [lt_mem_nhds hr₀] with y hy
    rw [jumpContribution_eq]
    exact (((c_hasDerivAt hy).mul_const A).add ((e_hasDerivAt hy).mul_const B)).deriv.trans
      (by rw [(c_hasDerivAt hy).deriv, (e_hasDerivAt hy).deriv])
  have hsecond := (((c_second_hasDerivAt hr₀).mul_const A).add
    ((e_second_hasDerivAt hr₀).mul_const B)).congr_of_eventuallyEq hfirst
  rw [hsecond.deriv, ← (c_second_hasDerivAt hr₀).deriv, ← (e_second_hasDerivAt hr₀).deriv]
  have hc := mul_nonpos_of_nonpos_of_nonneg (c_second_nonpos hr hhi) hA
  have he : deriv (deriv e) r * B ≤ 4 * (1-l)^3 := calc
    _ ≤ |deriv (deriv e) r * B| := le_abs_self _
    _ = |deriv (deriv e) r| * |B| := abs_mul _ _
    _ ≤ 1 * (4 * (1-l)^3) := mul_le_mul (e_second_abs_le hr) hB (abs_nonneg _) (by norm_num)
    _ = _ := one_mul _
  linarith

private def centeredEntropy (u v w : ℝ) : ℝ :=
  let T := u + v + w + 1
  T * Real.log (T / 4) - u * Real.log u - v * Real.log v - w * Real.log w

private theorem centeredEntropy_abs_le {a u v w : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hu' : a ≤ u ∧ u ≤ 1) (hv' : a ≤ v ∧ v ≤ 1) (hw' : a ≤ w ∧ w ≤ 1) :
    |centeredEntropy u v w| ≤ 6 * (1 - a) ^ 2 / (u + v + w + 1) := by
  let T := u + v + w + 1
  have hT : 0 < T := by dsimp [T]; positivity
  have h₄ : 0 < T / 4 := by positivity
  have H (z : ℝ) (hz : 0 < z) :
      z - 4 * z ^ 2 / T ≤ z * (Real.log (T / 4) - Real.log z) ∧
      z * (Real.log (T / 4) - Real.log z) ≤ T / 4 - z := by
    rw [← Real.log_div h₄.ne' hz.ne']
    have hp : 0 < T / 4 / z := by positivity
    constructor
    · refine le_trans ?_ (mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hp) hz.le)
      apply le_of_eq
      rw [inv_div]
      field_simp [hT.ne']
    · refine (mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hp) hz.le).trans_eq ?_
      field_simp [hz.ne']
  have hsum : centeredEntropy u v w =
      u * (Real.log (T / 4) - Real.log u) + v * (Real.log (T / 4) - Real.log v) +
      w * (Real.log (T / 4) - Real.log w) + 1 * (Real.log (T / 4) - Real.log 1) := by
    simp only [centeredEntropy, ← show T = u + v + w + 1 from rfl, Real.log_one, sub_zero]
    dsimp only [T]
    ring
  have hnonpos : centeredEntropy u v w ≤ 0 := by
    rw [hsum]
    linarith only [(H u hu).2, (H v hv).2, (H w hw).2, (H 1 zero_lt_one).2,
      show T = u + v + w + 1 from rfl]
  have hpair {x y : ℝ} (hx : a ≤ x ∧ x ≤ 1) (hy : a ≤ y ∧ y ≤ 1) :
      (x - y) ^ 2 ≤ (1 - a) ^ 2 := by
    rw [← sq_abs (x - y)]
    apply pow_le_pow_left₀ (abs_nonneg _)
    rw [abs_le]
    exact ⟨by linarith [hx.1, hy.2], by linarith [hy.1, hx.2]⟩
  have h₁ : a ≤ 1 ∧ (1 : ℝ) ≤ 1 := ⟨hu'.1.trans hu'.2, le_rfl⟩
  rw [abs_of_nonpos hnonpos]
  apply (le_div_iff₀ hT).2
  have hval : -centeredEntropy u v w ≤
      (4 * u ^ 2 / T + 4 * v ^ 2 / T + 4 * w ^ 2 / T + 4 * (1 : ℝ) ^ 2 / T) - T := by
    rw [hsum]
    linarith only [(H u hu).1, (H v hv).1, (H w hw).1, (H 1 zero_lt_one).1,
      show T = u + v + w + 1 from rfl]
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_right hval hT.le
    _ = (u-v)^2 + (u-w)^2 + (u-1)^2 + (v-w)^2 + (v-1)^2 + (w-1)^2 := by
      field_simp [hT.ne']
      dsimp only [T]
      ring
    _ ≤ _ := by
      linarith only [hpair hu' hv', hpair hu' hw', hpair hu' h₁,
        hpair hv' hw', hpair hv' h₁, hpair hw' h₁]

private theorem normalizedDeficit_second_eq (U : unitary Mat) {m n q r : ℝ}
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hq : 0 ≤ q) (hr : 1 < r) :
    deriv (deriv (fun y => normalizedDeficit y U m n q)) r =
      deriv (deriv h) r * totalAt m n q +
        deriv (deriv alpha) r * centeredEntropy (m^3) (n^3) (q^3) +
        deriv (deriv (jumpContribution U m n q)) r +
        deriv (deriv (fun y => bias y * spectralCharge U m n q)) r := by
  let T := totalAt m n q
  let Q := centeredEntropy (m^3) (n^3) (q^3)
  let J := jumpContribution U m n q
  let C := spectralCharge U m n q
  let F := fun y => h y * T + alpha y * Q + J y + bias y * C
  have heq : (fun y => normalizedDeficit y U m n q) =ᶠ[𝓝 r] F := by
    filter_upwards [lt_mem_nhds hr] with y hy
    exact normalizedDeficit_eq_jumpContribution U hy.le hm hn hq
  have hfirst : ∀ᶠ y in 𝓝 r, deriv F y =
      deriv h y * T + deriv alpha y * Q + deriv J y + deriv bias y * C := by
    filter_upwards [lt_mem_nhds hr] with y hy
    have hy₀ := zero_lt_one.trans hy
    have hh := h_hasDerivAt hy
    have ha := alpha_hasDerivAt hy
    have hb := bias_hasDerivAt hy₀
    exact (((((hh.congr_deriv hh.deriv.symm).mul_const T).fun_add
      ((ha.congr_deriv ha.deriv.symm).mul_const Q)).fun_add
      (jumpContribution_hasDerivAt U m n q hy₀)).fun_add
      ((hb.congr_deriv hb.deriv.symm).mul_const C)).deriv
  have hr₀ := zero_lt_one.trans hr
  have hh := h_second_hasDerivAt hr
  have ha := alpha_second_hasDerivAt hr
  have hb := bias_second_hasDerivAt hr₀
  have H := (((((hh.congr_deriv hh.deriv.symm).mul_const T).fun_add
    ((ha.congr_deriv ha.deriv.symm).mul_const Q)).fun_add
    (jumpContribution_second_hasDerivAt U m n q hr₀)).fun_add
    ((hb.congr_deriv hb.deriv.symm).mul_const C)).congr_of_eventuallyEq hfirst
  rw [heq.deriv.deriv_eq, H.deriv]
  simp only [deriv_mul_const_field']
  rfl

/-- The pure thermal curvature on the fixed spectral frame obeys both replay bounds.
`Tminus` and `Tplus` bound the total cubic mass throughout the spectral box. -/
theorem normalizedDeficit_second_le (U : unitary Mat) {m n q l r Tminus Tplus : ℝ}
    (hl : 0 < l) (hm : l ≤ m ∧ m ≤ 1) (hn : l ≤ n ∧ n ≤ 1) (hq : l ≤ q ∧ q ≤ 1)
    (hr : 1 < r) (hhi : r ≤ 6 / 5)
    (hminus₀ : 0 < Tminus) (hminus : Tminus ≤ totalAt m n q) (hplus : totalAt m n q ≤ Tplus) :
    deriv (deriv (fun y => normalizedDeficit y U m n q)) r ≤
      min 80 (11 * Tplus + 18 * (1 - l^3) + 6 * (1 - l^3)^2 / Tminus + 4 * (1 - l)^3) := by
  have hm₀ := hl.trans_le hm.1
  have hn₀ := hl.trans_le hn.1
  have hq₀ := hl.trans_le hq.1
  have hm₃ : l^3 ≤ m^3 ∧ m^3 ≤ 1 :=
    ⟨pow_le_pow_left₀ hl.le hm.1 3, by simpa using pow_le_pow_left₀ hm₀.le hm.2 3⟩
  have hn₃ : l^3 ≤ n^3 ∧ n^3 ≤ 1 :=
    ⟨pow_le_pow_left₀ hl.le hn.1 3, by simpa using pow_le_pow_left₀ hn₀.le hn.2 3⟩
  have hq₃ : l^3 ≤ q^3 ∧ q^3 ≤ 1 :=
    ⟨pow_le_pow_left₀ hl.le hq.1 3, by simpa using pow_le_pow_left₀ hq₀.le hq.2 3⟩
  let T := totalAt m n q
  let Q := centeredEntropy (m^3) (n^3) (q^3)
  have hT₀ : 0 < T := hminus₀.trans_le hminus
  have hT₁ : 1 ≤ T := by
    dsimp [T, totalAt]
    linarith only [pow_nonneg hm₀.le 3, pow_nonneg hn₀.le 3, pow_nonneg hq₀.le 3]
  have hT₄ : T ≤ 4 := by
    dsimp [T, totalAt]
    linarith only [hm₃.2, hn₃.2, hq₃.2]
  have hQ : |Q| ≤ 6 * (1 - l^3)^2 / T :=
    centeredEntropy_abs_le (pow_pos hm₀ 3) (pow_pos hn₀ 3) (pow_pos hq₀ 3) hm₃ hn₃ hq₃
  have hH := mul_le_mul_of_nonneg_right (h_second_le hr hhi) hT₀.le
  have hE : deriv (deriv alpha) r * Q ≤ 6 * (1 - l^3)^2 / T := calc
    _ ≤ |deriv (deriv alpha) r * Q| := le_abs_self _
    _ = |deriv (deriv alpha) r| * |Q| := abs_mul _ _
    _ ≤ _ := by simpa only [one_mul] using
      mul_le_mul (alpha_second_abs_le hr hhi) hQ (abs_nonneg _) (by norm_num)
  have hJ := jumpContribution_second_le U hl hm hn hq hr.le hhi
  have hB := (le_abs_self _).trans (biasContribution_second_abs_le U hl hm hn hq hr.le)
  have H : deriv (deriv (fun y => normalizedDeficit y U m n q)) r ≤
      11 * T + 18 * (1 - l^3) + 6 * (1 - l^3)^2 / T + 4 * (1 - l)^3 := by
    rw [normalizedDeficit_second_eq U hm₀.le hn₀.le hq₀.le hr]
    change _ + deriv (deriv alpha) r * Q + _ + _ ≤ _
    linarith
  refine H.trans (le_min ?_ ?_)
  · have hL := hm.1.trans hm.2
    have hL₃ : l^3 ≤ 1 := by simpa using pow_le_pow_left₀ hl.le hL 3
    have h₃ : (1 - l)^3 ≤ 1 := by
      simpa using pow_le_pow_left₀ (sub_nonneg.mpr hL) (show 1 - l ≤ 1 by linarith) 3
    have h₂ : (1 - l^3)^2 ≤ 1 := by
      simpa using pow_le_pow_left₀ (sub_nonneg.mpr hL₃)
        (show 1 - l^3 ≤ 1 by linarith [pow_nonneg hl.le 3]) 2
    have hFrac : 6 * (1 - l^3)^2 / T ≤ 6 := by
      rw [div_le_iff₀ hT₀]
      linarith
    linarith [pow_nonneg hl.le 3]
  · have hFrac := div_le_div_of_nonneg_left (show 0 ≤ 6 * (1 - l^3)^2 by positivity) hminus₀ hminus
    linarith

end D5.S3.Quantum.Semigroups.WuCubicBoundaryThermal
