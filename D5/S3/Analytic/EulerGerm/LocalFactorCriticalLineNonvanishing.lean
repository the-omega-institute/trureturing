/- GID: D5/S3/Analytic/EulerGerm/LocalFactorCriticalLineNonvanishing
   generality: I
   mirror-B: D5/B/S3/Analytic/EulerGerm/LocalFactorCriticalLineNonvanishing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime local factors at least five do not vanish on the pulled-back critical line. -/

import D5.S3.Analytic.EulerGerm.GoldenLocalFactor
import D5.S3.Analytic.GoldenEulerBeta

/-!
# Critical-line nonvanishing of golden local factors

The excited modes are bounded by a rational envelope at the smallest relevant
prime. A triangle estimate then excludes a zero at every prime at least five.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.EulerGerm.LocalFactorCriticalLineNonvanishing

open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor

noncomputable section

local notation "criticalSigma" =>
  (1 / (2 * Real.goldenRatio ^ 2) : Real)

private theorem criticalSigma_pos : 0 < criticalSigma := by
  positivity

private theorem natCast_le_o5Beta (v : Nat) :
    (v : Real) <= o5Beta v := by
  cases v with
  | zero => simp [o5_beta_zero]
  | succ v =>
      have hgrowth := o5_beta_growth (v + 1)
      have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : Real) :=
        Real.sq_sqrt (by norm_num)
      have hsqrt_nonneg : 0 <= Real.sqrt 5 := Real.sqrt_nonneg 5
      have hsqrt_two : 2 < Real.sqrt 5 := by nlinarith
      have hinv_pos : 0 < 1 / Real.goldenRatio :=
        one_div_pos.mpr Real.goldenRatio_pos
      push_cast at hgrowth ⊢
      nlinarith

private theorem real_local_factor_summable {sigma : Real}
    (hsigma : 0 < sigma) (p : Nat) (hp : p.Prime) :
    Summable (fun v : Nat => (p : Real) ^ (-sigma * o5Beta v)) := by
  let q : Real := (p : Real) ^ (-sigma)
  have hp_one : (1 : Real) <= p := by exact_mod_cast hp.one_lt.le
  have hp_pos : (0 : Real) < p := by exact_mod_cast hp.pos
  have hq_nonneg : 0 <= q := Real.rpow_nonneg hp_pos.le _
  have hq_lt_one : q < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast hp.one_lt) (neg_neg_of_pos hsigma)
  have hq_norm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq_nonneg]
    exact hq_lt_one
  have hgeom : Summable (fun v : Nat => q ^ v) :=
    summable_geometric_of_norm_lt_one hq_norm
  apply Summable.of_nonneg_of_le
    (fun _ => Real.rpow_nonneg hp_pos.le _)
    (fun v => ?_) hgeom
  have hexponent : -sigma * o5Beta v <= -sigma * (v : Real) := by
    nlinarith [natCast_le_o5Beta v]
  calc
    (p : Real) ^ (-sigma * o5Beta v) <=
        (p : Real) ^ (-sigma * (v : Real)) :=
      Real.rpow_le_rpow_of_exponent_le hp_one hexponent
    _ = q ^ v := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp_pos.le]

private theorem germLocalFactor_ne_zero_of_triangle {s : Complex}
    (p : Nat) (hp : p.Prime) (hs : 0 < s.re)
    (hsmall :
      (∑' v : Nat,
        ‖(p : Complex) ^ (-s * (o5Beta (v + 1) : Complex))‖) < 1) :
    germLocalFactor s p ≠ 0 := by
  have hreal := real_local_factor_summable hs p hp
  have hnorm : Summable (fun v : Nat =>
      ‖(p : Complex) ^ (-s * (o5Beta (v + 1) : Complex))‖) := by
    have hrealTail : Summable (fun v : Nat =>
        (p : Real) ^ (-s.re * o5Beta (v + 1))) := by
      simpa [Nat.add_comm] using
        (summable_nat_add_iff
          (f := fun v : Nat => (p : Real) ^ (-s.re * o5Beta v)) 1).2 hreal
    refine hrealTail.congr fun v => ?_
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
  have hcomplexTail : Summable (fun v : Nat =>
      (p : Complex) ^ (-s * (o5Beta (v + 1) : Complex))) := hnorm.of_norm
  have hcomplex : Summable (fun v : Nat =>
      (p : Complex) ^ (-s * (o5Beta v : Complex))) := by
    exact (summable_nat_add_iff
      (f := fun v : Nat =>
        (p : Complex) ^ (-s * (o5Beta v : Complex))) 1).1
      (by simpa [Nat.add_comm] using hcomplexTail)
  rw [germLocalFactor, hcomplex.tsum_eq_zero_add,
    o5_beta_zero]
  intro hzero
  simp only [Complex.ofReal_zero, mul_zero, Complex.cpow_zero] at hzero
  have htail_eq :
      (∑' v : Nat,
        (p : Complex) ^ (-s * (o5Beta (v + 1) : Complex))) = -1 := by
    linear_combination hzero
  have hnorm_tsum := norm_tsum_le_tsum_norm hnorm
  rw [htail_eq, norm_neg, norm_one] at hnorm_tsum
  exact (not_lt_of_ge hnorm_tsum) hsmall

private theorem goldenRatio_gt_eight_fifths :
    (8 : Real) / 5 < Real.goldenRatio := by
  rw [Real.goldenRatio]
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : Real) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 <= Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

private theorem goldenRatio_lt_five_thirds :
    Real.goldenRatio < (5 : Real) / 3 := by
  rw [Real.goldenRatio]
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : Real) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 <= Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

private theorem floor_two_mul_goldenRatio :
    ⌊(2 : Real) * Real.goldenRatio⌋ = (3 : Int) := by
  rw [Int.floor_eq_iff]
  constructor <;> norm_num at * <;>
    nlinarith [goldenRatio_gt_eight_fifths, goldenRatio_lt_five_thirds]

private theorem floor_three_mul_goldenRatio :
    ⌊(3 : Real) * Real.goldenRatio⌋ = (4 : Int) := by
  rw [Int.floor_eq_iff]
  constructor <;> norm_num at * <;>
    nlinarith [goldenRatio_gt_eight_fifths, goldenRatio_lt_five_thirds]

private theorem floor_four_mul_goldenRatio :
    ⌊(4 : Real) * Real.goldenRatio⌋ = (6 : Int) := by
  rw [Int.floor_eq_iff]
  constructor <;> norm_num at * <;>
    nlinarith [goldenRatio_gt_eight_fifths, goldenRatio_lt_five_thirds]

private theorem floor_five_mul_goldenRatio :
    ⌊(5 : Real) * Real.goldenRatio⌋ = (8 : Int) := by
  rw [Int.floor_eq_iff]
  constructor <;> norm_num at * <;>
    nlinarith [goldenRatio_gt_eight_fifths, goldenRatio_lt_five_thirds]

private theorem sqrt_five_eq_two_mul_goldenRatio_sub_one :
    Real.sqrt 5 = 2 * Real.goldenRatio - 1 := by
  rw [Real.goldenRatio]
  ring

private theorem one_div_goldenRatio_eq_goldenRatio_sub_one :
    1 / Real.goldenRatio = Real.goldenRatio - 1 := by
  rw [one_div, Real.inv_goldenRatio]
  linarith [Real.goldenRatio_add_goldenConj]

private theorem goldenRatio_cube :
    Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
  calc
    Real.goldenRatio ^ 3 =
        Real.goldenRatio * Real.goldenRatio ^ 2 := by ring
    _ = Real.goldenRatio * (Real.goldenRatio + 1) := by
      rw [Real.goldenRatio_sq]
    _ = 2 * Real.goldenRatio + 1 := by
      nlinarith [Real.goldenRatio_sq]

private theorem goldenRatio_fourth :
    Real.goldenRatio ^ 4 = 3 * Real.goldenRatio + 2 := by
  calc
    Real.goldenRatio ^ 4 = (Real.goldenRatio ^ 2) ^ 2 := by ring
    _ = (Real.goldenRatio + 1) ^ 2 := by rw [Real.goldenRatio_sq]
    _ = 3 * Real.goldenRatio + 2 := by
      nlinarith [Real.goldenRatio_sq]

private theorem o5_beta_one_closed_form :
    o5Beta 1 = Real.goldenRatio ^ 2 := by
  rw [o5_beta_closed_form, one_div_goldenRatio_eq_goldenRatio_sub_one]
  norm_num
  rw [Int.fract, floor_two_mul_goldenRatio,
    sqrt_five_eq_two_mul_goldenRatio_sub_one]
  norm_num
  ring

private theorem o5_beta_two_closed_form :
    o5Beta 2 = Real.goldenRatio ^ 3 := by
  rw [o5_beta_closed_form, one_div_goldenRatio_eq_goldenRatio_sub_one]
  norm_num
  rw [Int.fract, floor_three_mul_goldenRatio,
    sqrt_five_eq_two_mul_goldenRatio_sub_one, goldenRatio_cube]
  norm_num
  ring

private theorem o5_beta_three_closed_form :
    o5Beta 3 = Real.goldenRatio ^ 4 := by
  rw [o5_beta_closed_form, one_div_goldenRatio_eq_goldenRatio_sub_one]
  norm_num
  rw [Int.fract, floor_four_mul_goldenRatio,
    sqrt_five_eq_two_mul_goldenRatio_sub_one, goldenRatio_fourth]
  norm_num
  ring

private theorem o5_beta_four_sharp :
    o5Beta 4 = 2 * Real.goldenRatio ^ 3 + 1 := by
  rw [o5_beta_closed_form, one_div_goldenRatio_eq_goldenRatio_sub_one]
  norm_num
  rw [Int.fract, floor_five_mul_goldenRatio,
    sqrt_five_eq_two_mul_goldenRatio_sub_one, goldenRatio_cube]
  norm_num
  ring

private theorem five_rpow_neg_half_lt_nine_twentieths :
    (5 : Real) ^ (-(1 / 2 : Real)) < 9 / 20 := by
  rw [← Real.rpow_lt_rpow_iff (Real.rpow_nonneg (by norm_num) _)
    (by positivity : (0 : Real) <= 9 / 20) (by norm_num : (0 : Real) < 2)]
  rw [← Real.rpow_mul (by norm_num : (0 : Real) <= 5)]
  norm_num [Real.rpow_neg_natCast, Real.rpow_natCast]

private theorem five_rpow_neg_four_fifths_lt_seven_twenty_fifths :
    (5 : Real) ^ (-(4 / 5 : Real)) < 7 / 25 := by
  rw [← Real.rpow_lt_rpow_iff (Real.rpow_nonneg (by norm_num) _)
    (by positivity : (0 : Real) <= 7 / 25) (by norm_num : (0 : Real) < 5)]
  rw [← Real.rpow_mul (by norm_num : (0 : Real) <= 5)]
  norm_num [Real.rpow_neg_natCast, Real.rpow_natCast]

private theorem five_rpow_neg_thirteen_tenths_lt_one_eighth :
    (5 : Real) ^ (-(13 / 10 : Real)) < 1 / 8 := by
  rw [← Real.rpow_lt_rpow_iff (Real.rpow_nonneg (by norm_num) _)
    (by positivity : (0 : Real) <= 1 / 8) (by norm_num : (0 : Real) < 10)]
  rw [← Real.rpow_mul (by norm_num : (0 : Real) <= 5)]
  norm_num [Real.rpow_neg_natCast, Real.rpow_natCast]

private theorem five_rpow_neg_nine_fifths_lt_three_fiftieths :
    (5 : Real) ^ (-(9 / 5 : Real)) < 3 / 50 := by
  rw [← Real.rpow_lt_rpow_iff (Real.rpow_nonneg (by norm_num) _)
    (by positivity : (0 : Real) <= 3 / 50) (by norm_num : (0 : Real) < 5)]
  rw [← Real.rpow_mul (by norm_num : (0 : Real) <= 5)]
  norm_num [Real.rpow_neg_natCast, Real.rpow_natCast]

private theorem five_rpow_neg_five_twelfths_lt_thirteen_twenty_fifths :
    (5 : Real) ^ (-(5 / 12 : Real)) < 13 / 25 := by
  rw [← Real.rpow_lt_rpow_iff (Real.rpow_nonneg (by norm_num) _)
    (by positivity : (0 : Real) <= 13 / 25) (by norm_num : (0 : Real) < 12)]
  rw [← Real.rpow_mul (by norm_num : (0 : Real) <= 5)]
  norm_num [Real.rpow_neg_natCast, Real.rpow_natCast]

private theorem criticalSigma_mul_golden_sq :
    criticalSigma * Real.goldenRatio ^ 2 = 1 / 2 := by
  field_simp [ne_of_gt Real.goldenRatio_pos]

private theorem criticalSigma_mul_golden_cube :
    criticalSigma * Real.goldenRatio ^ 3 = Real.goldenRatio / 2 := by
  rw [show Real.goldenRatio ^ 3 =
      Real.goldenRatio ^ 2 * Real.goldenRatio by ring]
  calc
    criticalSigma * (Real.goldenRatio ^ 2 * Real.goldenRatio) =
        (criticalSigma * Real.goldenRatio ^ 2) * Real.goldenRatio := by ring
    _ = Real.goldenRatio / 2 := by
      rw [criticalSigma_mul_golden_sq]
      ring

private theorem criticalSigma_mul_golden_fourth :
    criticalSigma * Real.goldenRatio ^ 4 = Real.goldenRatio ^ 2 / 2 := by
  rw [show Real.goldenRatio ^ 4 =
      Real.goldenRatio ^ 2 * Real.goldenRatio ^ 2 by ring]
  calc
    criticalSigma * (Real.goldenRatio ^ 2 * Real.goldenRatio ^ 2) =
        (criticalSigma * Real.goldenRatio ^ 2) * Real.goldenRatio ^ 2 := by ring
    _ = Real.goldenRatio ^ 2 / 2 := by
      rw [criticalSigma_mul_golden_sq]
      ring

private theorem criticalSigma_mul_beta_four_gt :
    (9 / 5 : Real) <
      criticalSigma * (2 * Real.goldenRatio ^ 3 + 1) := by
  have hden : 0 < 2 * Real.goldenRatio ^ 2 := by positivity
  have hcube : Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
    calc
      Real.goldenRatio ^ 3 =
          Real.goldenRatio * Real.goldenRatio ^ 2 := by ring
      _ = Real.goldenRatio * (Real.goldenRatio + 1) := by
        rw [Real.goldenRatio_sq]
      _ = 2 * Real.goldenRatio + 1 := by
        nlinarith [Real.goldenRatio_sq]
  rw [show 1 / (2 * Real.goldenRatio ^ 2) *
      (2 * Real.goldenRatio ^ 3 + 1) =
      (2 * Real.goldenRatio ^ 3 + 1) /
        (2 * Real.goldenRatio ^ 2) by
    rw [div_eq_mul_inv]
    ring]
  rw [lt_div_iff₀ hden, hcube, Real.goldenRatio_sq]
  nlinarith [Real.one_lt_goldenRatio]

private theorem criticalSigma_mul_growth_start_gt_two :
    (2 : Real) < criticalSigma *
      (Real.sqrt 5 * 5 + 1 / Real.goldenRatio - 1) := by
  have hden : 0 < 2 * Real.goldenRatio ^ 2 := by positivity
  have hsqrt : Real.sqrt 5 = 2 * Real.goldenRatio - 1 := by
    rw [Real.goldenRatio]
    ring
  have hinv : 1 / Real.goldenRatio = Real.goldenRatio - 1 := by
    rw [one_div, Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  rw [show 1 / (2 * Real.goldenRatio ^ 2) *
      (Real.sqrt 5 * 5 + 1 / Real.goldenRatio - 1) =
      (Real.sqrt 5 * 5 + 1 / Real.goldenRatio - 1) /
        (2 * Real.goldenRatio ^ 2) by
    rw [div_eq_mul_inv]
    ring]
  rw [lt_div_iff₀ hden, hsqrt, hinv, Real.goldenRatio_sq]
  nlinarith [goldenRatio_gt_eight_fifths]

private theorem criticalSigma_mul_sqrt_five_gt_five_twelfths :
    (5 / 12 : Real) < criticalSigma * Real.sqrt 5 := by
  have hden : 0 < 2 * Real.goldenRatio ^ 2 := by positivity
  have hsqrt : Real.sqrt 5 = 2 * Real.goldenRatio - 1 := by
    rw [Real.goldenRatio]
    ring
  rw [show 1 / (2 * Real.goldenRatio ^ 2) * Real.sqrt 5 =
      Real.sqrt 5 / (2 * Real.goldenRatio ^ 2) by
    rw [div_eq_mul_inv]
    ring]
  rw [lt_div_iff₀ hden, hsqrt, Real.goldenRatio_sq]
  nlinarith [goldenRatio_gt_eight_fifths]

private theorem critical_mode_one_lt_nine_twentieths :
    (5 : Real) ^ (-criticalSigma * o5Beta 1) < 9 / 20 := by
  rw [o5_beta_one_closed_form]
  rw [show -criticalSigma * Real.goldenRatio ^ 2 = -(1 / 2 : Real) by
    rw [neg_mul, criticalSigma_mul_golden_sq]]
  exact five_rpow_neg_half_lt_nine_twentieths

private theorem critical_mode_two_lt_seven_twenty_fifths :
    (5 : Real) ^ (-criticalSigma * o5Beta 2) < 7 / 25 := by
  rw [o5_beta_two_closed_form]
  rw [show -criticalSigma * Real.goldenRatio ^ 3 =
      -(Real.goldenRatio / 2) by
    rw [neg_mul, criticalSigma_mul_golden_cube]]
  calc
    (5 : Real) ^ (-(Real.goldenRatio / 2)) <
        (5 : Real) ^ (-(4 / 5 : Real)) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by
        nlinarith [goldenRatio_gt_eight_fifths])
    _ < 7 / 25 :=
      five_rpow_neg_four_fifths_lt_seven_twenty_fifths

private theorem critical_mode_three_lt_one_eighth :
    (5 : Real) ^ (-criticalSigma * o5Beta 3) < 1 / 8 := by
  rw [o5_beta_three_closed_form]
  rw [show -criticalSigma * Real.goldenRatio ^ 4 =
      -(Real.goldenRatio ^ 2 / 2) by
    rw [neg_mul, criticalSigma_mul_golden_fourth]]
  have hphi_sq : (13 / 5 : Real) < Real.goldenRatio ^ 2 := by
    rw [Real.goldenRatio_sq]
    nlinarith [goldenRatio_gt_eight_fifths]
  calc
    (5 : Real) ^ (-(Real.goldenRatio ^ 2 / 2)) <
        (5 : Real) ^ (-(13 / 10 : Real)) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by
        nlinarith)
    _ < 1 / 8 := five_rpow_neg_thirteen_tenths_lt_one_eighth

private theorem critical_mode_four_lt_three_fiftieths :
    (5 : Real) ^ (-criticalSigma * o5Beta 4) < 3 / 50 := by
  rw [o5_beta_four_sharp]
  calc
    (5 : Real) ^
        (-criticalSigma * (2 * Real.goldenRatio ^ 3 + 1)) <
        (5 : Real) ^ (-(9 / 5 : Real)) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by
        nlinarith [criticalSigma_mul_beta_four_gt])
    _ < 3 / 50 := five_rpow_neg_nine_fifths_lt_three_fiftieths

private theorem critical_five_tail_from_five_lt_one_twelfth :
    (∑' k : Nat,
      (5 : Real) ^ (-criticalSigma * o5Beta (k + 5))) < 1 / 12 := by
  let B : Real := Real.sqrt 5 * 5 + 1 / Real.goldenRatio - 1
  let A : Real := (5 : Real) ^ (-criticalSigma * B)
  let q : Real := (5 : Real) ^ (-criticalSigma * Real.sqrt 5)
  have hA_nonneg : 0 <= A := by dsimp [A]; positivity
  have hq_nonneg : 0 <= q := by dsimp [q]; positivity
  have hA_lt : A < 1 / 25 := by
    dsimp [A]
    calc
      (5 : Real) ^ (-criticalSigma * B) < (5 : Real) ^ (-2 : Real) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by
          dsimp [B]
          nlinarith [criticalSigma_mul_growth_start_gt_two])
      _ = 1 / 25 := by
        norm_num [Real.rpow_neg_natCast, Real.rpow_natCast]
  have hq_lt : q < 13 / 25 := by
    dsimp [q]
    calc
      (5 : Real) ^ (-criticalSigma * Real.sqrt 5) <
          (5 : Real) ^ (-(5 / 12 : Real)) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by
          nlinarith [criticalSigma_mul_sqrt_five_gt_five_twelfths])
      _ < 13 / 25 :=
        five_rpow_neg_five_twelfths_lt_thirteen_twenty_fifths
  have hq_lt_one : q < 1 := hq_lt.trans (by norm_num)
  have hterm (k : Nat) :
      (5 : Real) ^ (-criticalSigma * o5Beta (k + 5)) <= A * q ^ k := by
    have hbeta : B + Real.sqrt 5 * (k : Real) <= o5Beta (k + 5) := by
      calc
        B + Real.sqrt 5 * (k : Real) =
            Real.sqrt 5 * ((k + 5 : Nat) : Real) +
              1 / Real.goldenRatio - 1 := by
          dsimp [B]
          push_cast
          ring
        _ <= o5Beta (k + 5) := o5_beta_growth (k + 5)
    calc
      (5 : Real) ^ (-criticalSigma * o5Beta (k + 5)) <=
          (5 : Real) ^
            (-criticalSigma * (B + Real.sqrt 5 * (k : Real))) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
          nlinarith [criticalSigma_pos])
      _ = A * q ^ k := by
        dsimp [A, q]
        rw [show -criticalSigma * (B + Real.sqrt 5 * (k : Real)) =
            (-criticalSigma * B) +
              (-criticalSigma * Real.sqrt 5) * (k : Real) by ring,
          Real.rpow_add (by norm_num : (0 : Real) < 5)]
        congr 1
        exact Real.rpow_mul_natCast (x := (5 : Real)) (by norm_num)
          (-criticalSigma * Real.sqrt 5) k
  have htail : Summable (fun k : Nat =>
      (5 : Real) ^ (-criticalSigma * o5Beta (k + 5))) := by
    simpa [Nat.add_comm] using
      (summable_nat_add_iff
        (f := fun v : Nat =>
          (5 : Real) ^ (-criticalSigma * o5Beta v)) 5).2
        (real_local_factor_summable criticalSigma_pos 5 (by norm_num))
  have hgeom : Summable (fun k : Nat => A * q ^ k) :=
    (summable_geometric_of_lt_one hq_nonneg hq_lt_one).mul_left A
  calc
    (∑' k : Nat,
        (5 : Real) ^ (-criticalSigma * o5Beta (k + 5))) <=
        ∑' k : Nat, A * q ^ k :=
      htail.tsum_le_tsum hterm hgeom
    _ = A * (1 - q)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq_nonneg hq_lt_one]
    _ = A / (1 - q) := by rw [div_eq_mul_inv]
    _ < 1 / 12 := by
      rw [div_lt_iff₀ (sub_pos.mpr hq_lt_one)]
      nlinarith

private theorem critical_five_excited_tsum_lt_one :
    (∑' v : Nat,
      (5 : Real) ^ (-criticalSigma * o5Beta (v + 1))) < 1 := by
  let f : Nat -> Real := fun v =>
    (5 : Real) ^ (-criticalSigma * o5Beta (v + 1))
  have hf : Summable f := by
    simpa [f, Nat.add_comm] using
      (summable_nat_add_iff
        (f := fun v : Nat =>
          (5 : Real) ^ (-criticalSigma * o5Beta v)) 1).2
        (real_local_factor_summable criticalSigma_pos 5 (by norm_num))
  have hprefix : (∑ v ∈ Finset.range 4, f v) < 183 / 200 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, f,
      Nat.reduceAdd]
    linarith [critical_mode_one_lt_nine_twentieths,
      critical_mode_two_lt_seven_twenty_fifths,
      critical_mode_three_lt_one_eighth,
      critical_mode_four_lt_three_fiftieths]
  have htail : (∑' k : Nat, f (k + 4)) < 1 / 12 := by
    simpa [f, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      critical_five_tail_from_five_lt_one_twelfth
  change (∑' v : Nat, f v) < 1
  calc
    (∑' v : Nat, f v) =
        (∑ v ∈ Finset.range 4, f v) + ∑' k : Nat, f (k + 4) :=
      (hf.sum_add_tsum_nat_add 4).symm
    _ < 183 / 200 + 1 / 12 := add_lt_add hprefix htail
    _ < 1 := by norm_num

private theorem critical_excited_real_tsum_lt_one {p : Nat}
    (hp : p.Prime) (h5 : 5 <= p) :
    (∑' v : Nat,
      (p : Real) ^ (-criticalSigma * o5Beta (v + 1))) < 1 := by
  have hp5 : (5 : Real) <= p := by exact_mod_cast h5
  have hpTail : Summable (fun v : Nat =>
      (p : Real) ^ (-criticalSigma * o5Beta (v + 1))) := by
    simpa [Nat.add_comm] using
      (summable_nat_add_iff
        (f := fun v : Nat =>
          (p : Real) ^ (-criticalSigma * o5Beta v)) 1).2
        (real_local_factor_summable criticalSigma_pos p hp)
  have hfiveTail : Summable (fun v : Nat =>
      (5 : Real) ^ (-criticalSigma * o5Beta (v + 1))) := by
    simpa [Nat.add_comm] using
      (summable_nat_add_iff
        (f := fun v : Nat =>
          (5 : Real) ^ (-criticalSigma * o5Beta v)) 1).2
        (real_local_factor_summable criticalSigma_pos 5 (by norm_num))
  calc
    (∑' v : Nat,
        (p : Real) ^ (-criticalSigma * o5Beta (v + 1))) <=
        ∑' v : Nat,
          (5 : Real) ^ (-criticalSigma * o5Beta (v + 1)) := by
      apply hpTail.tsum_le_tsum
      · intro v
        apply Real.rpow_le_rpow_of_nonpos (by norm_num) hp5
        have hbeta : 0 <= o5Beta (v + 1) :=
          (Nat.cast_nonneg (v + 1)).trans (natCast_le_o5Beta (v + 1))
        exact mul_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr criticalSigma_pos.le) hbeta
      · exact hfiveTail
    _ < 1 := critical_five_excited_tsum_lt_one

private theorem germLocalFactor_nonzero_of_five_le_of_criticalSigma_le_re
    {p : Nat} (hp : p.Prime) (h5 : 5 <= p) {s : Complex}
    (hs : criticalSigma <= s.re) : germLocalFactor s p ≠ 0 := by
  have hspos : 0 < s.re := criticalSigma_pos.trans_le hs
  apply germLocalFactor_ne_zero_of_triangle p hp hspos
  have hpTail : Summable (fun v : Nat =>
      (p : Real) ^ (-s.re * o5Beta (v + 1))) := by
    simpa [Nat.add_comm] using
      (summable_nat_add_iff
        (f := fun v : Nat =>
          (p : Real) ^ (-s.re * o5Beta v)) 1).2
        (real_local_factor_summable hspos p hp)
  have hcriticalTail : Summable (fun v : Nat =>
      (p : Real) ^ (-criticalSigma * o5Beta (v + 1))) := by
    simpa [Nat.add_comm] using
      (summable_nat_add_iff
        (f := fun v : Nat =>
          (p : Real) ^ (-criticalSigma * o5Beta v)) 1).2
        (real_local_factor_summable criticalSigma_pos p hp)
  have hrealSmall :
      (∑' v : Nat, (p : Real) ^ (-s.re * o5Beta (v + 1))) < 1 := by
    calc
      (∑' v : Nat, (p : Real) ^ (-s.re * o5Beta (v + 1))) <=
          ∑' v : Nat,
            (p : Real) ^ (-criticalSigma * o5Beta (v + 1)) := by
        apply hpTail.tsum_le_tsum
        · intro v
          apply Real.rpow_le_rpow_of_exponent_le
            (by exact_mod_cast hp.one_lt.le)
          have hbeta : 0 <= o5Beta (v + 1) :=
            (Nat.cast_nonneg (v + 1)).trans (natCast_le_o5Beta (v + 1))
          nlinarith
        · exact hcriticalTail
      _ < 1 := critical_excited_real_tsum_lt_one hp h5
  simpa only [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero] using hrealSmall

example : Nat.Prime 5 ∧ 5 ≤ 5 := by norm_num

example : ℝ := 0

/-- Local factors of primes `p >= 5` do not vanish on the pulled-back
critical line `Re(s) = 1 / (2 * phi^2)`. No claim is made for `p = 2` or
`p = 3`. -/
theorem germLocalFactor_critical_line_nonzero_of_five_le
    {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (t : ℝ) :
    germLocalFactor ((((1 / (2 * Real.goldenRatio ^ 2) : ℝ) : ℂ) +
      Complex.I * (t : ℂ))) p ≠ 0 := by
  apply germLocalFactor_nonzero_of_five_le_of_criticalSigma_le_re hp h5
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul,
    mul_zero, sub_zero, add_zero]
  exact le_rfl

#print axioms germLocalFactor_critical_line_nonzero_of_five_le

end

end D5.S3.Analytic.EulerGerm.LocalFactorCriticalLineNonvanishing
