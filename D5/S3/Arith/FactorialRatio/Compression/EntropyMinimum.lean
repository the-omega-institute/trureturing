/- GID: D5/S3/Arith/FactorialRatio/Compression/EntropyMinimum
   generality: I
   mirror-B: D5/B/S3/Arith/FactorialRatio/Compression/EntropyMinimum
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Log.Deriv]
   utility: none
   digest: Certified rational enclosures locate the entropy minimizer and its value. -/

import D5.S3.Arith.FactorialRatio.Compression.EntropyProfile
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Rational logarithm estimates and supporting lines enclose the actual profile minimum. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.FactorialRatio.Compression.EntropyMinimum

open Real Set Filter Finset
open scoped Topology
open D5.S3.Arith.FactorialRatio.Compression.EntropyProfile

private abbrev lowerPoint : ℝ := 7607566 / 10000000
private abbrev upperPoint : ℝ := 76075661 / 100000000

private theorem rational_log_bounds {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (n : ℕ) :
    let z := (1 - a) / (1 + a);
    -2 * ((∑ i ∈ range n, z ^ (2 * i + 1) / (2 * i + 1)) +
      z ^ (2 * n + 1) / (1 - z ^ 2)) ≤ log a ∧
    log a ≤ -2 * (∑ i ∈ range n, z ^ (2 * i + 1) / (2 * i + 1)) := by
  let z := (1 - a) / (1 + a)
  have hden : 0 < 1 + a := by linarith
  have hz : 0 ≤ z := div_nonneg (sub_nonneg.mpr ha1) hden.le
  have hz1 : z < 1 := (div_lt_one hden).mpr (by linarith)
  have hplus : 1 + z = 2 / (1 + a) := by dsimp [z]; field_simp; ring
  have hminus : 1 - z = 2 * a / (1 + a) := by dsimp [z]; field_simp; ring
  have heq : (1 + z) / (1 - z) = a⁻¹ := by
    rw [hplus, hminus]
    field_simp [ha.ne', hden.ne']
  have hlo := sum_range_le_log_div hz hz1 n
  have hhi := log_div_le_sum_range_add hz hz1 n
  rw [heq, log_inv] at hlo hhi
  change -2 * _ ≤ log a ∧ log a ≤ -2 * _
  constructor <;> linarith

private theorem lower_logs :
    (-2734418146 / 10000000000 : ℝ) ≤ log lowerPoint ∧
      log lowerPoint ≤ (-2734418145 / 10000000000 : ℝ) := by
  have h := rational_log_bounds (a := lowerPoint) (by norm_num) (by norm_num) 7
  norm_num [lowerPoint, Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

private theorem upper_logs :
    (-2734418015 / 10000000000 : ℝ) ≤ log upperPoint ∧
      log upperPoint ≤ (-2734418014 / 10000000000 : ℝ) := by
  have h := rational_log_bounds (a := upperPoint) (by norm_num) (by norm_num) 7
  norm_num [upperPoint, Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

private theorem lower_complement_logs :
    (-14302738358 / 10000000000 : ℝ) ≤ log (1 - lowerPoint) ∧
      log (1 - lowerPoint) ≤ (-14302738347 / 10000000000 : ℝ) := by
  have h := rational_log_bounds (a := 4 * (1 - lowerPoint)) (by norm_num) (by norm_num) 4
  have hsmall : (-439794742 / 10000000000 : ℝ) ≤ log (4 * (1 - lowerPoint)) ∧
      log (4 * (1 - lowerPoint)) ≤ (-439794741 / 10000000000 : ℝ) := by
    norm_num [lowerPoint, Finset.sum_range_succ] at h ⊢
    constructor <;> linarith [h.1, h.2]
  have hfour : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    norm_num
  have heq := log_mul (x := (4 : ℝ)) (y := 1 - lowerPoint)
    (by norm_num) (by norm_num [lowerPoint])
  rw [hfour] at heq
  have hlo := Real.log_two_gt_d9
  have hhi := Real.log_two_lt_d9
  norm_num [lowerPoint] at hsmall heq hlo hhi ⊢
  constructor <;> linarith only [heq, hsmall.1, hsmall.2, hlo, hhi]

private theorem upper_complement_logs :
    (-14302738776 / 10000000000 : ℝ) ≤ log (1 - upperPoint) ∧
      log (1 - upperPoint) ≤ (-14302738765 / 10000000000 : ℝ) := by
  have h := rational_log_bounds (a := 4 * (1 - upperPoint)) (by norm_num) (by norm_num) 4
  have hsmall : (-439795160 / 10000000000 : ℝ) ≤ log (4 * (1 - upperPoint)) ∧
      log (4 * (1 - upperPoint)) ≤ (-439795159 / 10000000000 : ℝ) := by
    norm_num [upperPoint, Finset.sum_range_succ] at h ⊢
    constructor <;> linarith [h.1, h.2]
  have hfour : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    norm_num
  have heq := log_mul (x := (4 : ℝ)) (y := 1 - upperPoint)
    (by norm_num) (by norm_num [upperPoint])
  rw [hfour] at heq
  have hlo := Real.log_two_gt_d9
  have hhi := Real.log_two_lt_d9
  norm_num [upperPoint] at hsmall heq hlo hhi ⊢
  constructor <;> linarith only [heq, hsmall.1, hsmall.2, hlo, hhi]

private def profileDerivative (t : ℝ) : ℝ :=
  (log t + (1 / t ^ 2 - 1) * log (1 - t) + 1 / t) / 2

private theorem profile_derivative {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt entropyIntegral (profileDerivative t) t := by
  let f : ℝ → ℝ := fun v => v / 2 * log v -
    (1 - v) ^ 2 / (2 * v) * log (1 - v) - 1 / 2
  have hd := (((((hasDerivAt_id t).div_const 2).mul (hasDerivAt_log ht.ne')).sub
    (((((hasDerivAt_id t).const_sub 1).pow 2).div
      ((hasDerivAt_id t).const_mul 2) (mul_ne_zero (by norm_num) ht.ne')).mul
      (((hasDerivAt_id t).const_sub 1).log (sub_pos.mpr ht1).ne'))).sub_const (1 / 2))
  have hdf : HasDerivAt f (profileDerivative t) t := by
    convert hd using 1
    · funext v
      dsimp [f] <;> ring
    · dsimp [profileDerivative]
      field_simp [ht.ne', (sub_pos.mpr ht1).ne'] <;> ring
  apply hdf.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht ht1] with v hv
  exact entropy_profile.2.2.2.1 v hv.1 hv.2.le

private theorem lower_estimates :
    -(1 / 1000 : ℝ) < profileDerivative lowerPoint ∧
      profileDerivative lowerPoint < 0 ∧
      (-550206239 / 1000000000 : ℝ) < entropyIntegral lowerPoint ∧
      entropyIntegral lowerPoint < (-550206236 / 1000000000 : ℝ) := by
  have ha := lower_logs
  have hb := lower_complement_logs
  have hv := entropy_profile.2.2.2.1 lowerPoint (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [profileDerivative, lowerPoint] at ha hb ⊢
    linarith [ha.1, ha.2, hb.1, hb.2]
  · norm_num [profileDerivative, lowerPoint] at ha hb ⊢
    linarith [ha.1, ha.2, hb.1, hb.2]
  · rw [hv]
    norm_num [lowerPoint] at ha hb ⊢
    linarith [ha.1, ha.2, hb.1, hb.2]
  · rw [hv]
    norm_num [lowerPoint] at ha hb ⊢
    linarith [ha.1, ha.2, hb.1, hb.2]

private theorem upper_derivative_pos : 0 < profileDerivative upperPoint := by
  have ha := upper_logs
  have hb := upper_complement_logs
  norm_num [profileDerivative, upperPoint] at ha hb ⊢
  linarith [ha.1, ha.2, hb.1, hb.2]

private theorem profile_support {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) (hd : HasDerivAt entropyIntegral (profileDerivative x) x) :
    profileDerivative x * (y - x) ≤ entropyIntegral y - entropyIntegral x := by
  rcases lt_trichotomy x y with h | rfl | h
  · have hh := profile_strictConvex.convexOn.le_slope_of_hasDerivAt hx hy h hd
    rw [slope_def_field] at hh
    exact (le_div_iff₀ (sub_pos.mpr h)).mp hh
  · simp
  · have hh := profile_strictConvex.convexOn.slope_le_of_hasDerivAt hy hx h hd
    rw [slope_def_field] at hh
    have hm := (div_le_iff₀ (sub_pos.mpr h)).mp hh
    nlinarith

/-- Every minimizer of the actual signed entropy integral has the stated
rational location and negative-value enclosures. -/
theorem entropy_minimum_enclosure {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hmin : ∀ v ∈ Icc (0 : ℝ) 1, entropyIntegral t ≤ entropyIntegral v) :
    (7607566 / 10000000 : ℝ) ≤ t ∧ t ≤ (76075661 / 100000000 : ℝ) ∧
      (55020623 / 100000000 : ℝ) < -entropyIntegral t ∧
      -entropyIntegral t < (55020624 / 100000000 : ℝ) := by
  have hL : lowerPoint ∈ Icc (0 : ℝ) 1 := by norm_num [lowerPoint]
  have hU : upperPoint ∈ Icc (0 : ℝ) 1 := by norm_num [upperPoint]
  have hdL := profile_derivative (t := lowerPoint) (by norm_num) (by norm_num)
  have hdU := profile_derivative (t := upperPoint) (by norm_num) (by norm_num)
  have hsL := profile_support hL ht hdL
  have hsU := profile_support hU ht hdU
  have hminL := hmin lowerPoint hL
  have hminU := hmin upperPoint hU
  have htL : lowerPoint ≤ t := by
    by_contra! h
    have hh := mul_pos_of_neg_of_neg lower_estimates.2.1 (sub_neg.mpr h)
    linarith
  have htU : t ≤ upperPoint := by
    by_contra! h
    have hh := mul_pos upper_derivative_pos (sub_pos.mpr h)
    linarith
  refine ⟨htL, htU, ?_, ?_⟩
  · have hvalue := lower_estimates.2.2.2
    norm_num [lowerPoint] at hvalue hminL ⊢
    linarith only [hminL, hvalue]
  · have herr : -(1 / 1000 : ℝ) * (upperPoint - lowerPoint) ≤
        profileDerivative lowerPoint * (t - lowerPoint) := calc
      _ ≤ -(1 / 1000 : ℝ) * (t - lowerPoint) :=
        mul_le_mul_of_nonpos_left (sub_le_sub_right htU lowerPoint) (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_right lower_estimates.1.le (sub_nonneg.mpr htL)
    have herr' : -(1 / 100000000000 : ℝ) ≤
        profileDerivative lowerPoint * (t - lowerPoint) := by
      convert herr using 1 <;> norm_num [lowerPoint, upperPoint]
    have hvalue := lower_estimates.2.2.1
    norm_num [lowerPoint] at hsL herr' hvalue ⊢
    linarith only [hsL, herr', hvalue]

end D5.S3.Arith.FactorialRatio.Compression.EntropyMinimum
