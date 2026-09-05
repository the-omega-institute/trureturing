/- GID: D5/S3/Analytic/GermWindow/GermJetModeLemma
   generality: I
   mirror-B: D5/B/S3/Analytic/GermWindow/GermJetModeLemma
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Enclose one golden germ mode and its derivative from rational data. -/

import D5.S3.Analytic.GermWindow.GermZeroCertificateReduction
import D5.S3.Analytic.Certified.TrigEnvelopePhaseReduction

/- Library-search audit trail (2026-09-05):
   * `rg -n "mode_term_enclosure|mode_deriv_enclosure" D5` found no D5 hit.
   * The same exact-name search in pinned Mathlib found no hit.
   * Shape searches for an exponential-times-trigonometric interval propagation
     theorem found no matching D5 or pinned-Mathlib declaration.
   * Pinned Mathlib supplies `Real.abs_log_sub_add_sum_range_le`,
     `Real.exp_bound`, `Real.exp_nat_mul`, and trigonometric Lipschitz bounds.
   * The frozen phase module supplies `abs_cos_sub_partial_le`,
     `abs_sin_sub_partial_le`, `exists_reduced_phase_pi_of_rat`,
     `abs_pi_sub_piApprox_lt`, and `o5Beta_eq_affine`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Complex
open scoped BigOperators
open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.GermWindow.GermZeroCertificateReduction
open D5.S3.Analytic.Certified.TrigEnvelopePhaseReduction

noncomputable section

namespace D5.S3.Analytic.GermWindow.GermJetModeLemma

private theorem golden_ratio_bounds_20 :
    (8090169943749474241 / 5000000000000000000 : ℝ) ≤
        Real.goldenRatio ∧
      Real.goldenRatio ≤
        (161803398874989484821 / 100000000000000000000 : ℝ) := by
  rw [Real.goldenRatio]
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  constructor <;> norm_num <;> nlinarith

/-- The seventy-term binary logarithm series has error at most `2⁻⁷⁰`.
This precision is sufficient for every mode through sixty. -/
theorem log_two_binary_70 :
    |Real.log 2 -
        (81026204946914272618346609082102250801114907729 /
          116896104058966015646750947554978314987992252416 : ℝ)| ≤
      1 / 2 ^ 70 := by
  have h := Real.abs_log_sub_add_sum_range_le
    (show |(2⁻¹ : ℝ)| < 1 by norm_num) 70
  rw [show (1 - (2⁻¹ : ℝ)) = 2⁻¹ by norm_num,
    Real.log_inv, ← sub_eq_add_neg, abs_sub_comm] at h
  have hsum :
      (∑ i ∈ Finset.range 70, (2⁻¹ : ℝ) ^ (i + 1) / (i + 1)) =
        (81026204946914272618346609082102250801114907729 /
          116896104058966015646750947554978314987992252416 : ℝ) := by
    norm_num [Finset.sum_range_succ]
  rw [hsum] at h
  convert h using 1
  all_goals norm_num

private theorem log_two_bounds_70 :
    (81026204946914272618247594230558639436210831195 /
        116896104058966015646750947554978314987992252416 : ℝ) ≤
        Real.log 2 ∧
      Real.log 2 ≤
        (81026204946914272618445623933645862166018984263 /
          116896104058966015646750947554978314987992252416 : ℝ) := by
  have h := log_two_binary_70
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

private theorem mode_term_re (v : ℕ) :
    ((2 : ℂ) ^ (-c * (o5Beta v : ℂ))).re =
      Real.exp (-(c.re * o5Beta v * Real.log 2)) *
        Real.cos (c.im * o5Beta v * Real.log 2) := by
  have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
    (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [Complex.cpow_def_of_ne_zero (by norm_num), hlog]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero,
    Complex.exp_re]
  ring_nf
  rw [Real.cos_neg]

private theorem mode_term_im (v : ℕ) :
    ((2 : ℂ) ^ (-c * (o5Beta v : ℂ))).im =
      -Real.exp (-(c.re * o5Beta v * Real.log 2)) *
        Real.sin (c.im * o5Beta v * Real.log 2) := by
  have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
    (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [Complex.cpow_def_of_ne_zero (by norm_num), hlog]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero,
    Complex.exp_im]
  ring_nf
  rw [Real.sin_neg]
  ring

private theorem mode_deriv_re (v : ℕ) :
    (-(o5Beta v : ℂ) * (Real.log 2 : ℂ) *
        (2 : ℂ) ^ (-c * (o5Beta v : ℂ))).re =
      -(Real.log 2 * o5Beta v) *
        ((2 : ℂ) ^ (-c * (o5Beta v : ℂ))).re := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

private theorem mode_deriv_im (v : ℕ) :
    (-(o5Beta v : ℂ) * (Real.log 2 : ℂ) *
        (2 : ℂ) ^ (-c * (o5Beta v : ℂ))).im =
      -(Real.log 2 * o5Beta v) *
        ((2 : ℂ) ^ (-c * (o5Beta v : ℂ))).im := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

private theorem abs_mul_approx_of_right_abs_le_one
    {x y x0 y0 ex ey : ℝ}
    (hx : |x - x0| ≤ ex) (hy : |y - y0| ≤ ey) (hy1 : |y| ≤ 1) :
    |x * y - x0 * y0| ≤ ex + |x0| * ey := by
  have hex : 0 ≤ ex := (abs_nonneg (x - x0)).trans hx
  have hey : 0 ≤ ey := (abs_nonneg (y - y0)).trans hy
  calc
    |x * y - x0 * y0| = |(x - x0) * y + x0 * (y - y0)| := by ring_nf
    _ ≤ |(x - x0) * y| + |x0 * (y - y0)| := abs_add_le _ _
    _ = |x - x0| * |y| + |x0| * |y - y0| := by rw [abs_mul, abs_mul]
    _ ≤ ex * 1 + |x0| * ey := by gcongr
    _ = ex + |x0| * ey := by ring

private theorem mode_term_coord_abs_le_one (v : ℕ) (hbeta : 0 ≤ o5Beta v) :
    |((2 : ℂ) ^ (-c * (o5Beta v : ℂ))).re| ≤ 1 ∧
      |((2 : ℂ) ^ (-c * (o5Beta v : ℂ))).im| ≤ 1 := by
  have hc : 0 ≤ c.re := by norm_num [c]
  have hl : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hx : 0 ≤ c.re * o5Beta v * Real.log 2 := mul_nonneg (mul_nonneg hc hbeta) hl
  have he : Real.exp (-(c.re * o5Beta v * Real.log 2)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_monotone (by linarith)
  have he0 := (Real.exp_pos (-(c.re * o5Beta v * Real.log 2))).le
  constructor
  · rw [mode_term_re, abs_mul, abs_of_nonneg he0]
    calc
      Real.exp (-(c.re * o5Beta v * Real.log 2)) *
          |Real.cos (c.im * o5Beta v * Real.log 2)| ≤ 1 * 1 := by
        gcongr
        exact Real.abs_cos_le_one _
      _ = 1 := by norm_num
  · rw [mode_term_im, abs_mul, abs_neg, abs_of_nonneg he0]
    calc
      Real.exp (-(c.re * o5Beta v * Real.log 2)) *
          |Real.sin (c.im * o5Beta v * Real.log 2)| ≤ 1 * 1 := by
        gcongr
        exact Real.abs_sin_le_one _
      _ = 1 := by norm_num

private theorem rational_width_cast {a b : ℚ}
    (h : b - a ≤ (1 / 10 ^ 15 : ℚ)) :
    (b : ℝ) - a ≤ 1 / 10 ^ 15 := by
  have hc : ((b - a : ℚ) : ℝ) ≤ (((1 / 10 ^ 15 : ℚ) : ℝ)) :=
    (Rat.cast_le).2 h
  norm_num at hc ⊢
  exact hc

private theorem exp_enclosure
    (x : ℝ) (scale : ℕ)
    (xLo xHi qLo qHi baseLo baseHi expLo expHi exp0 expErr : ℚ)
    (hx : (xLo : ℝ) ≤ x ∧ x ≤ (xHi : ℝ))
    (hscale : 0 < scale)
    (hqLo : (qLo : ℝ) ≤ -(xHi : ℝ) / scale)
    (hqHi : -(xLo : ℝ) / scale ≤ (qHi : ℝ))
    (hqLoAbs : |(qLo : ℝ)| ≤ 1) (hqHiAbs : |(qHi : ℝ)| ≤ 1)
    (hbaseLo :
      (baseLo : ℝ) ≤
        (∑ i ∈ Finset.range 20, (qLo : ℝ) ^ i / i.factorial) -
          |(qLo : ℝ)| ^ 20 * 21 / ((Nat.factorial 20 : ℝ) * 20))
    (hbaseHi :
      (∑ i ∈ Finset.range 20, (qHi : ℝ) ^ i / i.factorial) +
          |(qHi : ℝ)| ^ 20 * 21 / ((Nat.factorial 20 : ℝ) * 20) ≤
            (baseHi : ℝ))
    (hbaseLo0 : 0 ≤ (baseLo : ℝ))
    (hexpLo : (expLo : ℝ) ≤ (baseLo : ℝ) ^ scale)
    (hexpHi : (baseHi : ℝ) ^ scale ≤ (expHi : ℝ))
    (hcenterLo : (exp0 : ℝ) - expErr ≤ expLo)
    (hcenterHi : (expHi : ℝ) ≤ exp0 + expErr) :
    |Real.exp (-x) - (exp0 : ℝ)| ≤ (expErr : ℝ) := by
  have hqlo : (qLo : ℝ) ≤ -x / scale := by
    have hs : (0 : ℝ) < scale := by exact_mod_cast hscale
    apply le_trans hqLo
    exact div_le_div_of_nonneg_right (neg_le_neg hx.2) hs.le
  have hqhi : -x / scale ≤ (qHi : ℝ) := by
    have hs : (0 : ℝ) < scale := by exact_mod_cast hscale
    exact (div_le_div_of_nonneg_right (neg_le_neg hx.1) hs.le).trans hqHi
  have hlo := Real.exp_bound (x := (qLo : ℝ)) (n := 20) hqLoAbs (by norm_num)
  have hhi := Real.exp_bound (x := (qHi : ℝ)) (n := 20) hqHiAbs (by norm_num)
  rw [abs_le] at hlo hhi
  have hbaseLo' : (baseLo : ℝ) ≤ Real.exp (qLo : ℝ) := by
    linarith [hlo.1]
  have hbaseHi' : Real.exp (qHi : ℝ) ≤ (baseHi : ℝ) := by
    linarith [hhi.2]
  have hid : Real.exp (-x) = (Real.exp (-x / scale)) ^ scale := by
    rw [← Real.exp_nat_mul]
    congr 1
    have hs0 : (scale : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hscale)
    field_simp
  have hb : (expLo : ℝ) ≤ Real.exp (-x) ∧ Real.exp (-x) ≤ expHi := by
    rw [hid]
    constructor
    · exact hexpLo.trans (pow_le_pow_left₀ hbaseLo0
        (hbaseLo'.trans (Real.exp_monotone hqlo)) scale)
    · exact (pow_le_pow_left₀ (Real.exp_pos _).le
        ((Real.exp_monotone hqhi).trans hbaseHi') scale).trans hexpHi
  rw [abs_le]
  constructor <;> linarith [hb.1, hb.2]

private theorem trig_enclosure
    (theta phase : ℝ) (swap : Bool)
    (phaseLo phaseHi r0 rDelta piErr cos0 sin0 cosBaseErr sinBaseErr
      cosErr sinErr thetaCos0 thetaSin0 thetaCosErr thetaSinErr : ℚ)
    (hphaseEq : phase = if swap then theta - Real.pi / 2 else theta)
    (hphase : (phaseLo : ℝ) ≤ phase ∧ phase ≤ (phaseHi : ℝ))
    (hsize : |phaseLo| ≤ 10 ^ 7)
    (hres : |phaseLo - (phaseIndexPi phaseLo : ℚ) * piApprox| +
        (phaseHi - phaseLo) ≤ 99 / 100)
    (hpiErr : |((phaseIndexPi phaseLo : ℤ) : ℝ)| * (1 / 10 ^ 19 : ℝ) ≤
      (piErr : ℝ))
    (hr0 : (r0 : ℝ) = ((phaseLo + phaseHi) / 2 : ℚ) -
      ((phaseIndexPi phaseLo : ℤ) : ℝ) * (piApprox : ℝ))
    (hrDelta : (((phaseHi - phaseLo) / 2 : ℚ) : ℝ) + piErr ≤ rDelta)
    (hr0Abs : |(r0 : ℝ)| ≤ 1)
    (hcosBase :
      |(r0 : ℝ)| ^ 20 / (Nat.factorial 20 : ℝ) +
          |(∑ i ∈ Finset.range 10,
            (-1 : ℝ) ^ i * (r0 : ℝ) ^ (2 * i) / ((2 * i).factorial : ℝ)) -
            (cos0 : ℝ)| ≤ (cosBaseErr : ℝ))
    (hsinBase :
      |(r0 : ℝ)| ^ 21 / (Nat.factorial 21 : ℝ) +
          |(∑ i ∈ Finset.range 10,
            (-1 : ℝ) ^ i * (r0 : ℝ) ^ (2 * i + 1) /
              ((2 * i + 1).factorial : ℝ)) - (sin0 : ℝ)| ≤
        (sinBaseErr : ℝ))
    (hcosErr : (rDelta : ℝ) + cosBaseErr ≤ cosErr)
    (hsinErr : (rDelta : ℝ) + sinBaseErr ≤ sinErr)
    (hcosCenter :
      (if swap then
          -((-1 : ℝ) ^ phaseIndexPi phaseLo) * (sin0 : ℝ)
        else ((-1 : ℝ) ^ phaseIndexPi phaseLo) * (cos0 : ℝ)) = thetaCos0)
    (hsinCenter :
      (if swap then
          ((-1 : ℝ) ^ phaseIndexPi phaseLo) * (cos0 : ℝ)
        else ((-1 : ℝ) ^ phaseIndexPi phaseLo) * (sin0 : ℝ)) = thetaSin0)
    (hcosThetaErr : (if swap then (sinErr : ℝ) else cosErr) ≤ thetaCosErr)
    (hsinThetaErr : (if swap then (cosErr : ℝ) else sinErr) ≤ thetaSinErr) :
    |Real.cos theta - (thetaCos0 : ℝ)| ≤ thetaCosErr ∧
      |Real.sin theta - (thetaSin0 : ℝ)| ≤ thetaSinErr := by
  obtain ⟨r, hperiodic⟩ := exists_reduced_phase_pi_of_rat
    phaseLo phaseHi phase hphase.1 hphase.2 hsize hres
  have hmid :
      |phase - ((((phaseLo + phaseHi) / 2 : ℚ) : ℝ))| ≤
        ((((phaseHi - phaseLo) / 2 : ℚ) : ℝ)) := by
    rw [abs_le]
    constructor <;> norm_num at hphase ⊢ <;> linarith [hphase.1, hphase.2]
  have hkpi :
      |((phaseIndexPi phaseLo : ℤ) : ℝ) *
          (Real.pi - (piApprox : ℝ))| ≤ (piErr : ℝ) := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left abs_pi_sub_piApprox_lt.le
      (abs_nonneg _)).trans hpiErr
  have hrexp :
      r - (r0 : ℝ) =
        (phase - ((((phaseLo + phaseHi) / 2 : ℚ) : ℝ))) -
          ((phaseIndexPi phaseLo : ℤ) : ℝ) *
            (Real.pi - (piApprox : ℝ)) := by
    have hr : r = phase - ((phaseIndexPi phaseLo : ℤ) : ℝ) * Real.pi := by
      linarith [hperiodic.1]
    rw [hr, hr0]
    ring
  have hrclose : |r - (r0 : ℝ)| ≤ (rDelta : ℝ) := by
    rw [hrexp]
    calc
      |(phase - ((((phaseLo + phaseHi) / 2 : ℚ) : ℝ))) -
          ((phaseIndexPi phaseLo : ℤ) : ℝ) *
            (Real.pi - (piApprox : ℝ))| ≤
          |phase - ((((phaseLo + phaseHi) / 2 : ℚ) : ℝ))| +
            |((phaseIndexPi phaseLo : ℤ) : ℝ) *
              (Real.pi - (piApprox : ℝ))| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le
            (phase - ((((phaseLo + phaseHi) / 2 : ℚ) : ℝ))) 0
            (((phaseIndexPi phaseLo : ℤ) : ℝ) *
              (Real.pi - (piApprox : ℝ)))
      _ ≤ ((((phaseHi - phaseLo) / 2 : ℚ) : ℝ)) + piErr :=
        add_le_add hmid hkpi
      _ ≤ (rDelta : ℝ) := hrDelta
  have hcos0 := abs_cos_sub_partial_le (r0 : ℝ) hr0Abs 10
  have hsin0 := abs_sin_sub_partial_le (r0 : ℝ) hr0Abs 10
  have hcosR0 : |Real.cos (r0 : ℝ) - (cos0 : ℝ)| ≤ cosBaseErr := by
    calc
      |Real.cos (r0 : ℝ) - (cos0 : ℝ)| ≤
          |Real.cos (r0 : ℝ) -
            ∑ i ∈ Finset.range 10,
              (-1 : ℝ) ^ i * (r0 : ℝ) ^ (2 * i) / ((2 * i).factorial : ℝ)| +
          |(∑ i ∈ Finset.range 10,
            (-1 : ℝ) ^ i * (r0 : ℝ) ^ (2 * i) / ((2 * i).factorial : ℝ)) -
            (cos0 : ℝ)| := abs_sub_le _ _ _
      _ ≤ |(r0 : ℝ)| ^ 20 / (Nat.factorial 20 : ℝ) +
          |(∑ i ∈ Finset.range 10,
            (-1 : ℝ) ^ i * (r0 : ℝ) ^ (2 * i) / ((2 * i).factorial : ℝ)) -
            (cos0 : ℝ)| := add_le_add hcos0 (le_refl _)
      _ ≤ (cosBaseErr : ℝ) := hcosBase
  have hsinR0 : |Real.sin (r0 : ℝ) - (sin0 : ℝ)| ≤ sinBaseErr := by
    calc
      |Real.sin (r0 : ℝ) - (sin0 : ℝ)| ≤
          |Real.sin (r0 : ℝ) -
            ∑ i ∈ Finset.range 10,
              (-1 : ℝ) ^ i * (r0 : ℝ) ^ (2 * i + 1) /
                ((2 * i + 1).factorial : ℝ)| +
          |(∑ i ∈ Finset.range 10,
            (-1 : ℝ) ^ i * (r0 : ℝ) ^ (2 * i + 1) /
              ((2 * i + 1).factorial : ℝ)) - (sin0 : ℝ)| := abs_sub_le _ _ _
      _ ≤ |(r0 : ℝ)| ^ 21 / (Nat.factorial 21 : ℝ) +
          |(∑ i ∈ Finset.range 10,
            (-1 : ℝ) ^ i * (r0 : ℝ) ^ (2 * i + 1) /
              ((2 * i + 1).factorial : ℝ)) - (sin0 : ℝ)| :=
        add_le_add hsin0 (le_refl _)
      _ ≤ (sinBaseErr : ℝ) := hsinBase
  have hcosR : |Real.cos r - (cos0 : ℝ)| ≤ cosErr := by
    calc
      |Real.cos r - (cos0 : ℝ)| ≤
          |Real.cos r - Real.cos (r0 : ℝ)| +
            |Real.cos (r0 : ℝ) - (cos0 : ℝ)| := abs_sub_le _ _ _
      _ ≤ |r - (r0 : ℝ)| + cosBaseErr :=
        add_le_add (Real.abs_cos_sub_cos_le _ _) hcosR0
      _ ≤ (rDelta : ℝ) + cosBaseErr := add_le_add hrclose (le_refl _)
      _ ≤ (cosErr : ℝ) := hcosErr
  have hsinR : |Real.sin r - (sin0 : ℝ)| ≤ sinErr := by
    calc
      |Real.sin r - (sin0 : ℝ)| ≤
          |Real.sin r - Real.sin (r0 : ℝ)| +
            |Real.sin (r0 : ℝ) - (sin0 : ℝ)| := abs_sub_le _ _ _
      _ ≤ |r - (r0 : ℝ)| + sinBaseErr :=
        add_le_add (Real.abs_sin_sub_sin_le _ _) hsinR0
      _ ≤ (rDelta : ℝ) + sinBaseErr := add_le_add hrclose (le_refl _)
      _ ≤ (sinErr : ℝ) := hsinErr
  have hsabs : |(-1 : ℝ) ^ phaseIndexPi phaseLo| = 1 := by
    rw [abs_zpow, abs_neg, abs_one, one_zpow]
  cases swap with
  | false =>
      simp at hphaseEq hcosCenter hsinCenter hcosThetaErr hsinThetaErr
      subst phase
      constructor
      · rw [hperiodic.2.2.1, ← hcosCenter, ← mul_sub, abs_mul, hsabs, one_mul]
        exact hcosR.trans (by exact_mod_cast hcosThetaErr)
      · rw [hperiodic.2.2.2, ← hsinCenter, ← mul_sub, abs_mul, hsabs, one_mul]
        exact hsinR.trans (by exact_mod_cast hsinThetaErr)
  | true =>
      simp at hphaseEq hcosCenter hsinCenter hcosThetaErr hsinThetaErr
      have htheta : theta = phase + Real.pi / 2 := by linarith
      constructor
      · rw [htheta, Real.cos_add_pi_div_two, hperiodic.2.2.2, ← hcosCenter]
        calc
          _ = |-(((-1 : ℝ) ^ phaseIndexPi phaseLo) *
                (Real.sin r - (sin0 : ℝ)))| := by
            congr 1
            all_goals ring
          _ = |((-1 : ℝ) ^ phaseIndexPi phaseLo) *
                (Real.sin r - (sin0 : ℝ))| := abs_neg _
          _ = |(-1 : ℝ) ^ phaseIndexPi phaseLo| *
              |Real.sin r - (sin0 : ℝ)| := abs_mul _ _
          _ = |Real.sin r - (sin0 : ℝ)| := by rw [hsabs, one_mul]
          _ ≤ (sinErr : ℝ) := hsinR
          _ ≤ (thetaCosErr : ℝ) := by exact_mod_cast hcosThetaErr
      · rw [htheta, Real.sin_add_pi_div_two, hperiodic.2.2.1,
          ← hsinCenter, ← mul_sub, abs_mul, hsabs, one_mul]
        exact hcosR.trans (by exact_mod_cast hsinThetaErr)

/-- Rational mode data, checked by exact arithmetic, encloses the real and
imaginary coordinates of one golden germ term. The returned intervals have
width at most `10⁻¹⁵`. -/
theorem mode_term_enclosure
    (v : ℕ) (hv : v ≤ 60) (scale : ℕ) (swap : Bool)
    (betaLo betaHi xLo xHi thetaLo thetaHi phaseLo phaseHi r0 rDelta piErr
      qLo qHi baseLo baseHi expLo expHi exp0 expErr cos0 sin0 cosBaseErr
      sinBaseErr cosErr sinErr thetaCos0 thetaSin0 thetaCosErr thetaSinErr
      termReLo termReHi termImLo termImHi : ℚ)
    (hbetaLo : (betaLo : ℝ) ≤
      ((o5FloorTable ⟨v, by omega⟩ : ℤ) : ℝ) - 1 - v +
        v * (8090169943749474241 / 5000000000000000000 : ℝ))
    (hbetaHi :
      ((o5FloorTable ⟨v, by omega⟩ : ℤ) : ℝ) - 1 - v +
          v * (161803398874989484821 / 100000000000000000000 : ℝ) ≤ betaHi)
    (hbetaLo0 : 0 ≤ (betaLo : ℝ))
    (hxLo : (xLo : ℝ) ≤ c.re * betaLo *
      (81026204946914272618247594230558639436210831195 /
        116896104058966015646750947554978314987992252416 : ℝ))
    (hxHi : c.re * betaHi *
      (81026204946914272618445623933645862166018984263 /
        116896104058966015646750947554978314987992252416 : ℝ) ≤ xHi)
    (hthetaLo : (thetaLo : ℝ) ≤ c.im * betaLo *
      (81026204946914272618247594230558639436210831195 /
        116896104058966015646750947554978314987992252416 : ℝ))
    (hthetaHi : c.im * betaHi *
      (81026204946914272618445623933645862166018984263 /
        116896104058966015646750947554978314987992252416 : ℝ) ≤ thetaHi)
    (hphaseLo : (phaseLo : ℝ) ≤ if swap then
      (thetaLo : ℝ) - (piApprox : ℝ) / 2 - (1 / (2 * 10 ^ 19) : ℝ)
      else thetaLo)
    (hphaseHi : (if swap then
      (thetaHi : ℝ) - (piApprox : ℝ) / 2 + (1 / (2 * 10 ^ 19) : ℝ)
      else thetaHi) ≤ phaseHi)
    (hscale : 0 < scale)
    (hqLo : (qLo : ℝ) ≤ -(xHi : ℝ) / scale)
    (hqHi : -(xLo : ℝ) / scale ≤ (qHi : ℝ))
    (hqLoAbs : |(qLo : ℝ)| ≤ 1) (hqHiAbs : |(qHi : ℝ)| ≤ 1)
    (hbaseLo : (baseLo : ℝ) ≤
      (∑ i ∈ Finset.range 20, (qLo : ℝ) ^ i / i.factorial) -
        |(qLo : ℝ)| ^ 20 * 21 / ((Nat.factorial 20 : ℝ) * 20))
    (hbaseHi :
      (∑ i ∈ Finset.range 20, (qHi : ℝ) ^ i / i.factorial) +
          |(qHi : ℝ)| ^ 20 * 21 / ((Nat.factorial 20 : ℝ) * 20) ≤ baseHi)
    (hbaseLo0 : 0 ≤ (baseLo : ℝ))
    (hexpLo : (expLo : ℝ) ≤ (baseLo : ℝ) ^ scale)
    (hexpHi : (baseHi : ℝ) ^ scale ≤ (expHi : ℝ))
    (hcenterLo : (exp0 : ℝ) - expErr ≤ expLo)
    (hcenterHi : (expHi : ℝ) ≤ exp0 + expErr)
    (hsize : |phaseLo| ≤ 10 ^ 7)
    (hres : |phaseLo - (phaseIndexPi phaseLo : ℚ) * piApprox| +
        (phaseHi - phaseLo) ≤ 99 / 100)
    (hpiErr : |((phaseIndexPi phaseLo : ℤ) : ℝ)| * (1 / 10 ^ 19 : ℝ) ≤
      (piErr : ℝ))
    (hr0 : (r0 : ℝ) = ((phaseLo + phaseHi) / 2 : ℚ) -
      ((phaseIndexPi phaseLo : ℤ) : ℝ) * (piApprox : ℝ))
    (hrDelta : (((phaseHi - phaseLo) / 2 : ℚ) : ℝ) + piErr ≤ rDelta)
    (hr0Abs : |(r0 : ℝ)| ≤ 1)
    (hcosBase : |(r0 : ℝ)| ^ 20 / (Nat.factorial 20 : ℝ) +
      |(∑ i ∈ Finset.range 10,
        (-1 : ℝ) ^ i * (r0 : ℝ) ^ (2 * i) / ((2 * i).factorial : ℝ)) -
        (cos0 : ℝ)| ≤ cosBaseErr)
    (hsinBase : |(r0 : ℝ)| ^ 21 / (Nat.factorial 21 : ℝ) +
      |(∑ i ∈ Finset.range 10,
        (-1 : ℝ) ^ i * (r0 : ℝ) ^ (2 * i + 1) /
          ((2 * i + 1).factorial : ℝ)) - (sin0 : ℝ)| ≤ sinBaseErr)
    (hcosErr : (rDelta : ℝ) + cosBaseErr ≤ cosErr)
    (hsinErr : (rDelta : ℝ) + sinBaseErr ≤ sinErr)
    (hcosCenter : (if swap then
        -((-1 : ℝ) ^ phaseIndexPi phaseLo) * (sin0 : ℝ)
      else ((-1 : ℝ) ^ phaseIndexPi phaseLo) * (cos0 : ℝ)) = thetaCos0)
    (hsinCenter : (if swap then
        ((-1 : ℝ) ^ phaseIndexPi phaseLo) * (cos0 : ℝ)
      else ((-1 : ℝ) ^ phaseIndexPi phaseLo) * (sin0 : ℝ)) = thetaSin0)
    (hcosThetaErr : (if swap then (sinErr : ℝ) else cosErr) ≤ thetaCosErr)
    (hsinThetaErr : (if swap then (cosErr : ℝ) else sinErr) ≤ thetaSinErr)
    (htermReLo : (termReLo : ℝ) ≤ exp0 * thetaCos0 -
      (expErr + |(exp0 : ℝ)| * thetaCosErr))
    (htermReHi : exp0 * thetaCos0 +
      (expErr + |(exp0 : ℝ)| * thetaCosErr) ≤ termReHi)
    (htermImLo : (termImLo : ℝ) ≤ -(exp0 * thetaSin0) -
      (expErr + |(exp0 : ℝ)| * thetaSinErr))
    (htermImHi : -(exp0 * thetaSin0) +
      (expErr + |(exp0 : ℝ)| * thetaSinErr) ≤ termImHi)
    (hreWidth : termReHi - termReLo ≤ (1 / 10 ^ 15 : ℚ))
    (himWidth : termImHi - termImLo ≤ (1 / 10 ^ 15 : ℚ)) :
    (((termReLo : ℝ) ≤ ((2 : ℂ) ^ (-c * (o5Beta v : ℂ))).re ∧
        ((2 : ℂ) ^ (-c * (o5Beta v : ℂ))).re ≤ termReHi) ∧
      ((termImLo : ℝ) ≤ ((2 : ℂ) ^ (-c * (o5Beta v : ℂ))).im ∧
        ((2 : ℂ) ^ (-c * (o5Beta v : ℂ))).im ≤ termImHi)) ∧
      ((termReHi : ℝ) - termReLo ≤ 1 / 10 ^ 15 ∧
        (termImHi : ℝ) - termImLo ≤ 1 / 10 ^ 15) := by
  have hphi := golden_ratio_bounds_20
  have hlog := log_two_bounds_70
  have hbeta : (betaLo : ℝ) ≤ o5Beta v ∧ o5Beta v ≤ (betaHi : ℝ) := by
    rw [o5Beta_eq_affine v hv]
    constructor
    · calc
        (betaLo : ℝ) ≤
            ((o5FloorTable ⟨v, by omega⟩ : ℤ) : ℝ) - 1 - v +
              v * (8090169943749474241 / 5000000000000000000 : ℝ) := hbetaLo
        _ ≤ ((o5FloorTable ⟨v, by omega⟩ : ℤ) : ℝ) - 1 - v +
              v * Real.goldenRatio := by gcongr; exact hphi.1
    · calc
        ((o5FloorTable ⟨v, by omega⟩ : ℤ) : ℝ) - 1 - v +
              v * Real.goldenRatio ≤
            ((o5FloorTable ⟨v, by omega⟩ : ℤ) : ℝ) - 1 - v +
              v * (161803398874989484821 / 100000000000000000000 : ℝ) := by
                gcongr; exact hphi.2
        _ ≤ (betaHi : ℝ) := hbetaHi
  have hbeta0 : 0 ≤ o5Beta v := hbetaLo0.trans hbeta.1
  have hx : (xLo : ℝ) ≤ c.re * o5Beta v * Real.log 2 ∧
      c.re * o5Beta v * Real.log 2 ≤ (xHi : ℝ) := by
    have hc : 0 ≤ c.re := by norm_num [c]
    constructor
    · calc
        (xLo : ℝ) ≤ c.re * betaLo *
            (81026204946914272618247594230558639436210831195 /
              116896104058966015646750947554978314987992252416 : ℝ) := hxLo
        _ ≤ c.re * o5Beta v * Real.log 2 := by
          gcongr
          · exact hbeta.1
          · exact hlog.1
    · calc
        c.re * o5Beta v * Real.log 2 ≤ c.re * betaHi *
            (81026204946914272618445623933645862166018984263 /
              116896104058966015646750947554978314987992252416 : ℝ) := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
            (mul_le_mul hbeta.2 hlog.2
              (Real.log_pos (by norm_num)).le (hbeta0.trans hbeta.2)) hc
        _ ≤ (xHi : ℝ) := hxHi
  have htheta : (thetaLo : ℝ) ≤ c.im * o5Beta v * Real.log 2 ∧
      c.im * o5Beta v * Real.log 2 ≤ (thetaHi : ℝ) := by
    have hc : 0 ≤ c.im := by norm_num [c]
    constructor
    · calc
        (thetaLo : ℝ) ≤ c.im * betaLo *
            (81026204946914272618247594230558639436210831195 /
              116896104058966015646750947554978314987992252416 : ℝ) := hthetaLo
        _ ≤ c.im * o5Beta v * Real.log 2 := by
          gcongr
          · exact hbeta.1
          · exact hlog.1
    · calc
        c.im * o5Beta v * Real.log 2 ≤ c.im * betaHi *
            (81026204946914272618445623933645862166018984263 /
              116896104058966015646750947554978314987992252416 : ℝ) := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
            (mul_le_mul hbeta.2 hlog.2
              (Real.log_pos (by norm_num)).le (hbeta0.trans hbeta.2)) hc
        _ ≤ (thetaHi : ℝ) := hthetaHi
  let theta : ℝ := c.im * o5Beta v * Real.log 2
  let phase : ℝ := if swap then theta - Real.pi / 2 else theta
  have hp := abs_pi_sub_piApprox_lt
  rw [abs_lt] at hp
  have hphase : (phaseLo : ℝ) ≤ phase ∧ phase ≤ (phaseHi : ℝ) := by
    dsimp [phase]
    cases swap with
    | false => simpa [theta] using ⟨hphaseLo.trans htheta.1, htheta.2.trans hphaseHi⟩
    | true =>
        simp only [↓reduceIte] at hphaseLo hphaseHi ⊢
        constructor
        · calc
            (phaseLo : ℝ) ≤ (thetaLo : ℝ) - (piApprox : ℝ) / 2 -
                (1 / (2 * 10 ^ 19) : ℝ) := hphaseLo
            _ ≤ theta - Real.pi / 2 := by
              dsimp [theta]
              linarith [htheta.1, hp.2]
        · calc
            theta - Real.pi / 2 ≤ (thetaHi : ℝ) - (piApprox : ℝ) / 2 +
                (1 / (2 * 10 ^ 19) : ℝ) := by
              dsimp [theta]
              linarith [htheta.2, hp.1]
            _ ≤ (phaseHi : ℝ) := hphaseHi
  have he := exp_enclosure (c.re * o5Beta v * Real.log 2) scale
    xLo xHi qLo qHi baseLo baseHi expLo expHi exp0 expErr hx hscale hqLo hqHi
    hqLoAbs hqHiAbs hbaseLo hbaseHi hbaseLo0 hexpLo hexpHi hcenterLo hcenterHi
  have ht := trig_enclosure theta phase swap phaseLo phaseHi r0 rDelta piErr
    cos0 sin0 cosBaseErr sinBaseErr cosErr sinErr thetaCos0 thetaSin0
    thetaCosErr thetaSinErr (by rfl) hphase hsize hres hpiErr hr0 hrDelta
    hr0Abs hcosBase hsinBase hcosErr hsinErr hcosCenter hsinCenter
    hcosThetaErr hsinThetaErr
  have hre :
      |((2 : ℂ) ^ (-c * (o5Beta v : ℂ))).re -
          ((exp0 : ℝ) * thetaCos0)| ≤
        (expErr : ℝ) + |(exp0 : ℝ)| * thetaCosErr := by
    rw [mode_term_re]
    change |Real.exp (-(c.re * o5Beta v * Real.log 2)) * Real.cos theta - _| ≤ _
    exact abs_mul_approx_of_right_abs_le_one he ht.1 (Real.abs_cos_le_one _)
  have him :
      |((2 : ℂ) ^ (-c * (o5Beta v : ℂ))).im -
          (-(exp0 : ℝ) * thetaSin0)| ≤
        (expErr : ℝ) + |(exp0 : ℝ)| * thetaSinErr := by
    rw [mode_term_im]
    change |(-Real.exp (-(c.re * o5Beta v * Real.log 2))) * Real.sin theta - _| ≤ _
    have he' : |-Real.exp (-(c.re * o5Beta v * Real.log 2)) - (-(exp0 : ℝ))| ≤
        (expErr : ℝ) := by
      simpa only [neg_sub_neg, abs_neg, abs_sub_comm] using he
    simpa only [abs_neg] using
      abs_mul_approx_of_right_abs_le_one he' ht.2 (Real.abs_sin_le_one _)
  rw [abs_le] at hre him
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · linarith [hre.1]
  · linarith [hre.2]
  · linarith [him.1]
  · linarith [him.2]
  · exact ⟨rational_width_cast hreWidth, rational_width_cast himWidth⟩

/-- A certified term enclosure and rational amplitude data enclose the matching
derivative term. The returned derivative intervals have width at most
`10⁻¹⁵`. -/
theorem mode_deriv_enclosure
    (v : ℕ) (hv : v ≤ 60)
    (betaLo betaHi exp0 thetaCos0 thetaSin0 termReErr termImErr
      termReLo termReHi termImLo termImHi amp0 ampErr
      derivReLo derivReHi derivImLo derivImHi : ℚ)
    (hbetaLo : (betaLo : ℝ) ≤
      ((o5FloorTable ⟨v, by omega⟩ : ℤ) : ℝ) - 1 - v +
        v * (8090169943749474241 / 5000000000000000000 : ℝ))
    (hbetaHi :
      ((o5FloorTable ⟨v, by omega⟩ : ℤ) : ℝ) - 1 - v +
          v * (161803398874989484821 / 100000000000000000000 : ℝ) ≤ betaHi)
    (hbetaLo0 : 0 ≤ (betaLo : ℝ))
    (hterm :
      (((termReLo : ℝ) ≤ ((2 : ℂ) ^ (-c * (o5Beta v : ℂ))).re ∧
          ((2 : ℂ) ^ (-c * (o5Beta v : ℂ))).re ≤ termReHi) ∧
        ((termImLo : ℝ) ≤ ((2 : ℂ) ^ (-c * (o5Beta v : ℂ))).im ∧
          ((2 : ℂ) ^ (-c * (o5Beta v : ℂ))).im ≤ termImHi)) ∧
        ((termReHi : ℝ) - termReLo ≤ 1 / 10 ^ 15 ∧
          (termImHi : ℝ) - termImLo ≤ 1 / 10 ^ 15))
    (hampLo : (amp0 : ℝ) - ampErr ≤
      (81026204946914272618247594230558639436210831195 /
        116896104058966015646750947554978314987992252416 : ℝ) * betaLo)
    (hampHi :
      (81026204946914272618445623933645862166018984263 /
        116896104058966015646750947554978314987992252416 : ℝ) * betaHi ≤
        amp0 + ampErr)
    (htermReLoApprox : exp0 * thetaCos0 - termReErr ≤ termReLo)
    (htermReHiApprox : (termReHi : ℝ) ≤ exp0 * thetaCos0 + termReErr)
    (htermImLoApprox : -(exp0 * thetaSin0) - termImErr ≤ termImLo)
    (htermImHiApprox : (termImHi : ℝ) ≤ -(exp0 * thetaSin0) + termImErr)
    (hderivReLo : (derivReLo : ℝ) ≤ -(amp0 * (exp0 * thetaCos0)) -
      (ampErr + |(amp0 : ℝ)| * termReErr))
    (hderivReHi : -(amp0 * (exp0 * thetaCos0)) +
      (ampErr + |(amp0 : ℝ)| * termReErr) ≤ derivReHi)
    (hderivImLo : (derivImLo : ℝ) ≤ -(amp0 * (-(exp0 * thetaSin0))) -
      (ampErr + |(amp0 : ℝ)| * termImErr))
    (hderivImHi : -(amp0 * (-(exp0 * thetaSin0))) +
      (ampErr + |(amp0 : ℝ)| * termImErr) ≤ derivImHi)
    (hreWidth : derivReHi - derivReLo ≤ (1 / 10 ^ 15 : ℚ))
    (himWidth : derivImHi - derivImLo ≤ (1 / 10 ^ 15 : ℚ)) :
    (((derivReLo : ℝ) ≤
        (-(o5Beta v : ℂ) * (Real.log 2 : ℂ) *
          (2 : ℂ) ^ (-c * (o5Beta v : ℂ))).re ∧
      (-(o5Beta v : ℂ) * (Real.log 2 : ℂ) *
          (2 : ℂ) ^ (-c * (o5Beta v : ℂ))).re ≤ derivReHi) ∧
      ((derivImLo : ℝ) ≤
        (-(o5Beta v : ℂ) * (Real.log 2 : ℂ) *
          (2 : ℂ) ^ (-c * (o5Beta v : ℂ))).im ∧
      (-(o5Beta v : ℂ) * (Real.log 2 : ℂ) *
          (2 : ℂ) ^ (-c * (o5Beta v : ℂ))).im ≤ derivImHi)) ∧
      ((derivReHi : ℝ) - derivReLo ≤ 1 / 10 ^ 15 ∧
        (derivImHi : ℝ) - derivImLo ≤ 1 / 10 ^ 15) := by
  have hphi := golden_ratio_bounds_20
  have hlog := log_two_bounds_70
  have hbeta : (betaLo : ℝ) ≤ o5Beta v ∧ o5Beta v ≤ (betaHi : ℝ) := by
    rw [o5Beta_eq_affine v hv]
    constructor
    · calc
        (betaLo : ℝ) ≤
            ((o5FloorTable ⟨v, by omega⟩ : ℤ) : ℝ) - 1 - v +
              v * (8090169943749474241 / 5000000000000000000 : ℝ) := hbetaLo
        _ ≤ ((o5FloorTable ⟨v, by omega⟩ : ℤ) : ℝ) - 1 - v +
              v * Real.goldenRatio := by gcongr; exact hphi.1
    · calc
        ((o5FloorTable ⟨v, by omega⟩ : ℤ) : ℝ) - 1 - v +
              v * Real.goldenRatio ≤
            ((o5FloorTable ⟨v, by omega⟩ : ℤ) : ℝ) - 1 - v +
              v * (161803398874989484821 / 100000000000000000000 : ℝ) := by
                gcongr; exact hphi.2
        _ ≤ (betaHi : ℝ) := hbetaHi
  have hbeta0 : 0 ≤ o5Beta v := hbetaLo0.trans hbeta.1
  have hamp : |Real.log 2 * o5Beta v - (amp0 : ℝ)| ≤ ampErr := by
    rw [abs_le]
    constructor
    · have hlo : (amp0 : ℝ) - ampErr ≤ Real.log 2 * o5Beta v := by
        exact hampLo.trans (mul_le_mul hlog.1 hbeta.1 hbetaLo0
          (Real.log_pos (by norm_num)).le)
      linarith
    · have hhi : Real.log 2 * o5Beta v ≤ (amp0 : ℝ) + ampErr := by
        exact (mul_le_mul hlog.2 hbeta.2 hbeta0
          (by positivity)).trans hampHi
      linarith
  have hcoord := mode_term_coord_abs_le_one v hbeta0
  have htermReLoApprox' :
      (exp0 : ℝ) * thetaCos0 - termReErr ≤ termReLo := by
    exact_mod_cast htermReLoApprox
  have htermImLoApprox' :
      -((exp0 : ℝ) * thetaSin0) - termImErr ≤ termImLo := by
    exact_mod_cast htermImLoApprox
  have htre :
      |((2 : ℂ) ^ (-c * (o5Beta v : ℂ))).re -
        ((exp0 : ℝ) * thetaCos0)| ≤ termReErr := by
    rw [abs_le]
    constructor <;> linarith [hterm.1.1.1, hterm.1.1.2,
      htermReLoApprox', htermReHiApprox]
  have htim :
      |((2 : ℂ) ^ (-c * (o5Beta v : ℂ))).im -
        (-(exp0 : ℝ) * thetaSin0)| ≤ termImErr := by
    rw [abs_le]
    constructor <;> linarith [hterm.1.2.1, hterm.1.2.2,
      htermImLoApprox', htermImHiApprox]
  have ha' : |-(Real.log 2 * o5Beta v) - (-(amp0 : ℝ))| ≤ ampErr := by
    simpa only [neg_sub_neg, abs_neg, abs_sub_comm] using hamp
  have hre := abs_mul_approx_of_right_abs_le_one ha' htre hcoord.1
  have him := abs_mul_approx_of_right_abs_le_one ha' htim hcoord.2
  rw [← mode_deriv_re] at hre
  rw [abs_le] at hre
  rw [← mode_deriv_im] at him
  rw [abs_le] at him
  simp only [abs_neg] at hre him
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · linarith [hre.1]
  · linarith [hre.2]
  · linarith [him.1]
  · linarith [him.2]
  · exact ⟨rational_width_cast hreWidth, rational_width_cast himWidth⟩

/- Fidelity and non-hollowness witnesses. -/
example : Nonempty (Fin 61) := ⟨⟨0, by norm_num⟩⟩

example :
    ∃ lo hi : ℚ, (lo : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (hi : ℝ) := by
  refine ⟨
    (81026204946914272618247594230558639436210831195 /
      116896104058966015646750947554978314987992252416 : ℚ),
    (81026204946914272618445623933645862166018984263 /
      116896104058966015646750947554978314987992252416 : ℚ), ?_⟩
  simpa using log_two_bounds_70

#print axioms log_two_binary_70
#print axioms mode_term_enclosure
#print axioms mode_deriv_enclosure

end D5.S3.Analytic.GermWindow.GermJetModeLemma
