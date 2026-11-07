/- GID: D5/S3/Weil/Mertens/Cryptids/DigammaBinet
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/Cryptids/DigammaBinet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original Cryptids DigammaBinet analytic source for the RH Chebyshev bound. -/

/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in
  docs/reports/licenses/cryptids-LICENSE.txt.
Source: https://github.com/google-deepmind/cryptids/blob/e5f59ed70d1549a61ef8873a6fbae9268fdbd557/Cryptids/Semantics/Riemann/DigammaBinet.lean
Routing adaptations: ordinary D5 modules, redirected imports, and declaration-boundary splitting.
The original declaration namespaces, statements, and mathematical proof text are retained.
Retirement: when this repository's lake-manifest.json Mathlib revision provides an equivalent
RH-only real-x Chebyshev psi estimate for x >= 5000, replace the target with that declaration
and delete the transplanted declarations no longer in its live dependency closure.
-/

import D5.S3.Weil.Mertens.Cryptids.DigammaBinet.Foundation

/-! Original DigammaBinet analytic supplier for the RH Chebyshev estimate. -/

namespace ConjectureMachines.Semantics.Riemann.DigammaBinet

open Complex Finset Filter MeasureTheory Set
open scoped Real Topology Interval ArithmeticFunction.vonMangoldt LSeries.notation

/-- For all `t : ℝ`, `riemannZeta ((-1 / 4 : ℂ) + (t : ℂ) * I) ≠ 0`. -/
theorem riemannZeta_leftVertical_ne_zero (t : ℝ) :
    riemannZeta ((-1 / 4 : ℂ) + (t : ℂ) * I) ≠ 0 := by
  set s : ℂ := (-1 / 4 : ℂ) + (t : ℂ) * I
  have h1s_re : 1 < (1 - s).re := by simp [s]; norm_num
  have h1s_nat : ∀ n : ℕ, 1 - s ≠ -(n : ℂ) := by
    intro n h
    have hre := congrArg Complex.re h
    simp only [neg_re, natCast_re] at hre
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h1s_one : 1 - s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [one_re] at hre
    linarith
  have h_fe := riemannZeta_one_sub h1s_nat h1s_one
  rw [sub_sub_cancel] at h_fe
  rw [h_fe]
  have h1 : (2 : ℂ) ≠ 0 := two_ne_zero
  have h2 : (2 * π : ℂ) ^ (-(1 - s)) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    left
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have h3 : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have h4 : Complex.cos (π * (1 - s) / 2) ≠ 0 := by
    intro hcos
    rw [Complex.cos_eq_zero_iff] at hcos
    obtain ⟨k, hk⟩ := hcos
    have hpi_ne : (π : ℂ) ≠ 0 := mod_cast Real.pi_ne_zero
    have h1s_eq : 1 - s = 2 * k + 1 := by
      apply mul_right_cancel₀ hpi_ne
      calc
        (1 - s) * π = (π * (1 - s) / 2) * 2 := by ring
        _ = ((2 * k + 1) * π / 2) * 2 := by rw [hk]
        _ = (2 * k + 1) * π := by ring
    exact leftVertical_ne_intCast t (-2 * k) (by push_cast; linear_combination -h1s_eq)
  have h5 : riemannZeta (1 - s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re h1s_re
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) h4) h5

/-- Bound on `‖Complex.log ((3 / 4 : ℂ) + (t : ℂ) * I)‖` for all `t : ℝ`:
`‖Complex.log ((3 / 4 : ℂ) + (t : ℂ) * I)‖ ≤ Real.log (|t| + 2) + Real.pi`. -/
theorem norm_log_three_fourths_add_mul_I_le (t : ℝ) :
    ‖Complex.log ((3 / 4 : ℂ) + (t : ℂ) * I)‖ ≤ Real.log (|t| + 2) + Real.pi := by
  set w : ℂ := (3 / 4 : ℂ) + (t : ℂ) * I
  have hw_re : w.re = 3 / 4 := by simp [w]
  have hw_im : w.im = t := by simp [w]
  have hw_norm_ge : 3 / 4 ≤ ‖w‖ := by
    have h := Complex.re_le_norm w
    linarith
  have hw_norm_le : ‖w‖ ≤ |t| + 2 := by
    have h := Complex.norm_le_abs_re_add_abs_im w
    rw [hw_re, hw_im, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4)] at h
    linarith
  have ht2_pos : 0 < |t| + 2 := by positivity
  have hw_norm_pos : 0 < ‖w‖ := by linarith
  have h_inv_le : (|t| + 2)⁻¹ ≤ ‖w‖ := by
    have h1 : (|t| + 2)⁻¹ ≤ (2 : ℝ)⁻¹ :=
      inv_anti₀ (by norm_num) (by linarith [abs_nonneg t])
    linarith
  have h_abs_log : |Real.log ‖w‖| ≤ Real.log (|t| + 2) := by
    rw [abs_le]
    refine ⟨?_, Real.log_le_log hw_norm_pos hw_norm_le⟩
    rw [← Real.log_inv]
    exact Real.log_le_log (by positivity) h_inv_le
  rw [← Complex.re_add_im (Complex.log w), Complex.log_re, Complex.log_im]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    norm_I, mul_one]
  exact add_le_add h_abs_log (Complex.abs_arg_le_pi w)

/-- Bound on `‖Complex.digamma ((-1 / 4 : ℂ) + (t : ℂ) * I)‖` for all `t : ℝ`:
$$\left\|\psi\!\left(-\frac{1}{4} + t i\right)\right\|
  \le \log(|t| + 2) + \pi + \frac{2 + \pi}{3} + 4.$$ -/
theorem norm_digamma_leftVertical_le (t : ℝ) :
    ‖Complex.digamma ((-1 / 4 : ℂ) + (t : ℂ) * I)‖ ≤
      Real.log (|t| + 2) + Real.pi + (2 + Real.pi) / 3 + 4 := by
  set s : ℂ := (-1 / 4 : ℂ) + (t : ℂ) * I
  set w : ℂ := (3 / 4 : ℂ) + (t : ℂ) * I
  have h_sw : s + 1 = w := by dsimp [s, w]; ring
  have hs_nat : ∀ m : ℕ, s ≠ -(m : ℂ) :=
    fun m ↦ by simpa using leftVertical_ne_intCast t (-m)
  have h_step : Complex.digamma s = (Complex.digamma w - Complex.log w) + Complex.log w - s⁻¹ := by
    have h := Complex.digamma_apply_add_one s hs_nat
    rw [h_sw] at h
    linear_combination -h
  have hw_re : 0 < w.re := by simp [w]
  have hw_norm : 3 / 4 ≤ ‖w‖ := by
    have h := Complex.re_le_norm w
    simp [w] at h
    linarith
  have hs_norm : 1 / 4 ≤ ‖s‖ := by
    have h := Complex.abs_re_le_norm s
    have hre : s.re = -1 / 4 := by simp [s]
    rw [hre] at h
    norm_num at h
    exact h
  have h1 : ‖Complex.digamma w - Complex.log w‖ ≤ (2 + Real.pi) / 3 := by
    refine (norm_digamma_sub_log_le_two_add_pi_div_four_norm hw_re).trans ?_
    exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  have h2 : ‖Complex.log w‖ ≤ Real.log (|t| + 2) + Real.pi :=
    norm_log_three_fourths_add_mul_I_le t
  have h3 : ‖s⁻¹‖ ≤ 4 := by
    rw [norm_inv]
    simpa using inv_anti₀ (by norm_num) hs_norm
  change ‖Complex.digamma s‖ ≤ _
  rw [h_step]
  have h_tri1 := norm_sub_le ((Complex.digamma w - Complex.log w) + Complex.log w) s⁻¹
  have h_tri2 := norm_add_le (Complex.digamma w - Complex.log w) (Complex.log w)
  linarith

/-- The explicit additive constant in the vertical growth bound for
`‖logDeriv riemannZeta (-1 / 4 + t * I)‖`. -/
noncomputable def leftVerticalLogDerivConst : ℝ :=
  ‖logDeriv riemannZeta (5 / 4 : ℂ)‖ + Real.log (2 * Real.pi) +
    Real.pi + (2 + Real.pi) / 3 + 4 + Real.pi / 2

/-- **Explicit Vertical Growth Bound for `logDeriv riemannZeta` on `s.re = -1 / 4`**:
For all `t : ℝ`,
$$\left\|\frac{\zeta'}{\zeta}\!\left(-\frac{1}{4} + t i\right)\right\|
  \le \log(|t| + 2) + C_{\text{left}}.$$ -/
theorem norm_logDeriv_riemannZeta_leftVertical_le (t : ℝ) :
    ‖logDeriv riemannZeta ((-1 / 4 : ℂ) + (t : ℂ) * I)‖ ≤
      Real.log (|t| + 2) + leftVerticalLogDerivConst := by
  set s : ℂ := (-1 / 4 : ℂ) + (t : ℂ) * I
  have h_fe :
      logDeriv riemannZeta s =
        -logDeriv riemannZeta (1 - s) + Complex.log (2 * π) - Complex.digamma s +
          π / 2 * Complex.tan (π * s / 2) :=
    logDeriv_riemannZeta_one_sub (leftVertical_ne_intCast t) (riemannZeta_leftVertical_ne_zero t)
  have h1s_re : (1 - s).re = 5 / 4 := by simp [s]; ring
  have h1 : ‖-logDeriv riemannZeta (1 - s)‖ ≤ ‖logDeriv riemannZeta (5 / 4 : ℂ)‖ := by
    rw [norm_neg]
    have h := norm_logDeriv_riemannZeta_le_of_one_lt_re (z := 1 - s) (by rw [h1s_re]; norm_num)
    rwa [h1s_re, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_ofNat] at h
  have h2 : ‖Complex.log (2 * π)‖ = Real.log (2 * Real.pi) := by
    have h_pos : (0 : ℝ) < 2 * Real.pi := by positivity
    rw [show (2 * π : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_log h_pos.le, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.log_pos (by linarith [Real.pi_gt_three]))]
  have h3 : ‖Complex.digamma s‖ ≤ Real.log (|t| + 2) + Real.pi + (2 + Real.pi) / 3 + 4 :=
    norm_digamma_leftVertical_le t
  have h4 : ‖(π : ℂ) / 2 * Complex.tan (π * s / 2)‖ ≤ Real.pi / 2 := by
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Complex.norm_ofNat]
    have h_tan : ‖Complex.tan (π * s / 2)‖ ≤ 1 :=
      (cos_ne_zero_and_norm_tan_le_one_leftVertical t).2
    nlinarith [Real.pi_pos]
  change ‖logDeriv riemannZeta s‖ ≤ _
  rw [h_fe]
  have h_tri1 :=
    norm_add_le (-logDeriv riemannZeta (1 - s) + Complex.log (2 * π) - Complex.digamma s)
      (π / 2 * Complex.tan (π * s / 2))
  have h_tri2 :=
    norm_sub_le (-logDeriv riemannZeta (1 - s) + Complex.log (2 * π)) (Complex.digamma s)
  have h_tri3 := norm_add_le (-logDeriv riemannZeta (1 - s)) (Complex.log (2 * π))
  unfold leftVerticalLogDerivConst
  linarith

/-- Telescoping majorant `64 / n ^ (1 / 8)` for `log n / n ^ (5 / 4)`. -/
noncomputable def rpowTelescope (n : ℕ) : ℝ :=
  if n = 0 then 0 else 64 / (n : ℝ) ^ (1 / 8 : ℝ)

theorem rpowTelescope_one : rpowTelescope 1 = 64 := by
  simp [rpowTelescope]

theorem rpowTelescope_nonneg (n : ℕ) : 0 ≤ rpowTelescope n := by
  unfold rpowTelescope
  split_ifs with hn
  · exact le_rfl
  · positivity

/-- For every `n ≥ 2`,
`Real.log (n : ℝ) / (n : ℝ) ^ (5 / 4 : ℝ) ≤ rpowTelescope (n - 1) - rpowTelescope n`. -/
theorem log_nat_div_rpow_five_fourths_le_rpowTelescope_sub {n : ℕ} (hn : 2 ≤ n) :
    Real.log (n : ℝ) / (n : ℝ) ^ (5 / 4 : ℝ) ≤ rpowTelescope (n - 1) - rpowTelescope n := by
  have hn0 : n ≠ 0 := by omega
  have hn1 : n - 1 ≠ 0 := by omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hn1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by positivity
  set a : ℝ := ((n - 1 : ℕ) : ℝ) ^ (1 / 8 : ℝ)
  set b : ℝ := (n : ℝ) ^ (1 / 8 : ℝ)
  have ha_pos : 0 < a := Real.rpow_pos_of_pos hn1_pos _
  have hb_pos : 0 < b := Real.rpow_pos_of_pos hn_pos _
  have hab : a ≤ b := by
    refine Real.rpow_le_rpow hn1_pos.le ?_ (by positivity)
    exact_mod_cast Nat.sub_le n 1
  have ha8 : a ^ 8 = ((n - 1 : ℕ) : ℝ) := by
    dsimp [a]
    rw [← Real.rpow_natCast _ 8, ← Real.rpow_mul hn1_pos.le]
    norm_num
  have hb8 : b ^ 8 = (n : ℝ) := by
    dsimp [b]
    rw [← Real.rpow_natCast _ 8, ← Real.rpow_mul hn_pos.le]
    norm_num
  have hb10 : b ^ 10 = (n : ℝ) ^ (5 / 4 : ℝ) := by
    dsimp [b]
    rw [← Real.rpow_natCast _ 10, ← Real.rpow_mul hn_pos.le]
    norm_num
  have hlog_le : Real.log (n : ℝ) ≤ 8 * b := by
    have hlog_b8 : Real.log (n : ℝ) = 8 * Real.log b := by
      rw [← hb8, Real.log_pow, Nat.cast_ofNat]
    have hlog_b : Real.log b ≤ b - 1 := Real.log_le_sub_one_of_pos hb_pos
    linarith
  have h_b8_sub_a8 : b ^ 8 - a ^ 8 = 1 := by
    rw [hb8, ha8, Nat.cast_sub (by omega), Nat.cast_one]
    ring
  have h_diff_ge : 1 ≤ 8 * b ^ 7 * (b - a) := by
    have h_ba : 0 ≤ b - a := sub_nonneg.mpr hab
    have h_ba1 : b + a ≤ 2 * b := by linarith
    have h_ba2 : b ^ 2 + a ^ 2 ≤ 2 * b ^ 2 := by
      have : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha_pos.le hab 2
      linarith
    have h_ba4 : b ^ 4 + a ^ 4 ≤ 2 * b ^ 4 := by
      have : a ^ 4 ≤ b ^ 4 := pow_le_pow_left₀ ha_pos.le hab 4
      linarith
    calc
      (1 : ℝ) = b ^ 8 - a ^ 8 := h_b8_sub_a8.symm
      _ = (b ^ 4 + a ^ 4) * (b ^ 2 + a ^ 2) * (b + a) * (b - a) := by ring
      _ ≤ (2 * b ^ 4) * (2 * b ^ 2) * (2 * b) * (b - a) := by
          gcongr
      _ = 8 * b ^ 7 * (b - a) := by ring
  have h_tele_eq : rpowTelescope (n - 1) - rpowTelescope n = 64 * (b - a) / (a * b) := by
    simp only [rpowTelescope, hn0, hn1, ↓reduceIte]
    change 64 / a - 64 / b = 64 * (b - a) / (a * b)
    have ha_ne : a ≠ 0 := ha_pos.ne'
    have hb_ne : b ≠ 0 := hb_pos.ne'
    field_simp
  rw [ ← hb10, h_tele_eq]
  calc
    Real.log (n : ℝ) / b ^ 10
      ≤ (8 * b) / b ^ 10 := by gcongr
    _ = 8 / b ^ 9 := by
        have hb_ne : b ≠ 0 := hb_pos.ne'
        field_simp [hb_ne]
    _ ≤ 64 * (b - a) / (a * b) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h_mul : a * b ≤ b ^ 2 * (8 * b ^ 7 * (b - a)) := by
          calc
            a * b ≤ b * b := by gcongr
            _ = b ^ 2 * 1 := by ring
            _ ≤ b ^ 2 * (8 * b ^ 7 * (b - a)) := by gcongr
        linarith

/-- For every `n ≥ 2`,
`‖LSeries.term ↗Λ (5 / 4 : ℂ) n‖ ≤ rpowTelescope (n - 1) - rpowTelescope n`. -/
theorem norm_term_vonMangoldt_five_fourths_le {n : ℕ} (hn : 2 ≤ n) :
    ‖LSeries.term (↗Λ) (5 / 4 : ℂ) n‖ ≤ rpowTelescope (n - 1) - rpowTelescope n := by
  rw [LSeries.norm_term_eq]
  have hn0 : n ≠ 0 := by omega
  simp only [hn0, ↓reduceIte, Complex.norm_real]
  rw [Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hre : (5 / 4 : ℂ).re = 5 / 4 := by norm_num
  rw [hre]
  refine (div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (by positivity)).trans ?_
  exact log_nat_div_rpow_five_fourths_le_rpowTelescope_sub hn

theorem sum_range_norm_term_vonMangoldt_five_fourths_le_sub :
    ∀ N : ℕ, 2 ≤ N →
      ∑ n ∈ Finset.range N, ‖LSeries.term (↗Λ) (5 / 4 : ℂ) n‖ ≤
        64 - rpowTelescope (N - 1) := by
  intro N hN
  induction N with
  | zero => omega
  | succ N ih =>
    rcases eq_or_lt_of_le hN with h_eq | h_lt
    · have hN1 : N = 1 := by omega
      subst hN1
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      simp [LSeries.term, rpowTelescope_one]
    · have hN2 : 2 ≤ N := by omega
      rw [Finset.sum_range_succ]
      have h1 := ih hN2
      have h2 := norm_term_vonMangoldt_five_fourths_le hN2
      rw [Nat.add_sub_cancel]
      linarith

theorem sum_range_norm_term_vonMangoldt_five_fourths_le (N : ℕ) :
    ∑ n ∈ Finset.range N, ‖LSeries.term (↗Λ) (5 / 4 : ℂ) n‖ ≤ 64 := by
  rcases lt_or_ge N 2 with hlt | hge
  · interval_cases N
    · simp
    · rw [Finset.sum_range_one, LSeries.term_zero, norm_zero]
      norm_num
  · have h := sum_range_norm_term_vonMangoldt_five_fourths_le_sub N hge
    have h_nonneg := rpowTelescope_nonneg (N - 1)
    linarith

/-- **Explicit Pure-Constant Bound on `‖logDeriv riemannZeta (5 / 4 : ℂ)‖`**:
$$\left\|\frac{\zeta'}{\zeta}\!\left(\frac{5}{4}\right)\right\| \le 64.$$ -/
theorem norm_logDeriv_riemannZeta_five_fourths_le :
    ‖logDeriv riemannZeta (5 / 4 : ℂ)‖ ≤ 64 := by
  have h_re : 1 < (5 / 4 : ℂ).re := by norm_num
  have h_eq : logDeriv riemannZeta (5 / 4 : ℂ) = -L (↗Λ) (5 / 4 : ℂ) := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div h_re, logDeriv_apply,
      neg_div, neg_neg]
  rw [h_eq, norm_neg]
  unfold LSeries
  have h_sum : Summable (fun n : ℕ ↦ ‖LSeries.term (↗Λ) (5 / 4 : ℂ) n‖) :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt h_re).norm
  refine (norm_tsum_le_tsum_norm h_sum).trans ?_
  exact h_sum.tsum_le_of_sum_range_le sum_range_norm_term_vonMangoldt_five_fourths_le

/-- Explicit upper bound `leftVerticalLogDerivConst ≤ 85`. -/
theorem leftVerticalLogDerivConst_le :
    leftVerticalLogDerivConst ≤ 85 := by
  unfold leftVerticalLogDerivConst
  have h1 := norm_logDeriv_riemannZeta_five_fourths_le
  have h_pi : Real.pi < 4 := Real.pi_lt_four
  have h_2pi_pos : 0 < 2 * Real.pi := by positivity
  have h_log : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 :=
    Real.log_le_sub_one_of_pos h_2pi_pos
  linarith

/-- **Explicit Pure-Constant Bound on `‖logDeriv riemannZeta (-1 / 4 + t * I)‖`**:
For all `t : ℝ`,
$$\left\|\frac{\zeta'}{\zeta}\!\left(-\frac{1}{4} + t i\right)\right\| \le \log(|t| + 2) + 85.$$ -/
theorem norm_logDeriv_riemannZeta_leftVertical_le_eighty_five (t : ℝ) :
    ‖logDeriv riemannZeta ((-1 / 4 : ℂ) + (t : ℂ) * I)‖ ≤ Real.log (|t| + 2) + 85 := by
  refine (norm_logDeriv_riemannZeta_leftVertical_le t).trans ?_
  linarith [leftVerticalLogDerivConst_le]

/-!
### Section 5B: Exact Vertical Integral of `Re(Complex.digamma (a + t * I))` on `[-U, U]`
-/

end ConjectureMachines.Semantics.Riemann.DigammaBinet
