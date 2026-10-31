/- GID: D5/S3/Weil/Mertens/Cryptids/ExplicitLarge
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/Cryptids/ExplicitLarge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original Cryptids ExplicitLarge analytic source for the RH Chebyshev bound. -/

/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in
  docs/reports/licenses/cryptids-LICENSE.txt.
Source: https://github.com/google-deepmind/cryptids/blob/e5f59ed70d1549a61ef8873a6fbae9268fdbd557/Cryptids/Semantics/Riemann/ExplicitLarge.lean
Routing adaptations: ordinary D5 modules, redirected imports, and declaration-boundary splitting.
The original declaration namespaces, statements, and mathematical proof text are retained.
Retirement: when this repository's lake-manifest.json Mathlib revision provides an equivalent
RH-only real-x Chebyshev psi estimate for x >= 5000, replace the target with that declaration
and delete the transplanted declarations no longer in its live dependency closure.
-/

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-! Original ExplicitLarge analytic supplier for the RH Chebyshev estimate. -/

namespace ConjectureMachines.Semantics.Riemann.ExplicitLarge


open Real

/-- For `x ≥ 5000`, `851 / 100 ≤ Real.log x` (via `2 ^ 86 ≤ 5000 ^ 7`). -/
lemma log_ge_851_div_100 {x : ℝ} (hx : 5000 ≤ x) :
    (851 / 100 : ℝ) ≤ Real.log x := by
  have hpow : (2 : ℝ) ^ (86 : ℕ) ≤ x ^ (7 : ℕ) := by
    have h1 : (2 : ℝ) ^ (86 : ℕ) ≤ (5000 : ℝ) ^ (7 : ℕ) := by norm_num
    have h2 : (5000 : ℝ) ^ (7 : ℕ) ≤ x ^ (7 : ℕ) := pow_le_pow_left₀ (by norm_num) hx 7
    exact h1.trans h2
  have hlog : Real.log ((2 : ℝ) ^ (86 : ℕ)) ≤ Real.log (x ^ (7 : ℕ)) :=
    Real.log_le_log (by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  have hlog2 := Real.log_two_gt_d9
  push_cast at hlog
  linarith

/-- For `x ≥ 5000`, `70 ≤ Real.sqrt x`. -/
lemma sqrt_ge_seventy {x : ℝ} (hx : 5000 ≤ x) :
    (70 : ℝ) ≤ Real.sqrt x := by
  have h70 : (70 : ℝ) ^ 2 ≤ x := by norm_num; linarith
  have hsqrt := Real.sqrt_le_sqrt h70
  rwa [Real.sqrt_sq (by norm_num)] at hsqrt

/-- For `v ≥ 851 / 400`, `(39 / 10) * v ≤ Real.exp v` via the degree-6 Taylor lower bound. -/
lemma exp_ge_thirty_nine_tenths_mul {v : ℝ} (hv : (851 / 400 : ℝ) ≤ v) :
    (39 / 10 : ℝ) * v ≤ Real.exp v := by
  have hv_nonneg : 0 ≤ v := by linarith
  have h_sum := Real.sum_le_exp_of_nonneg hv_nonneg 7
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial,
    Nat.cast_one, Nat.cast_mul, pow_zero, pow_one, zero_add] at h_sum
  have h_amgm : 0 ≤ (v / 2 - 1) ^ 2 := sq_nonneg (v / 2 - 1)
  have h_v2 : (851 / 400 : ℝ) ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ (by norm_num) hv 2
  have h_v3 : (851 / 400 : ℝ) ^ 3 ≤ v ^ 3 := pow_le_pow_left₀ (by norm_num) hv 3
  have h_v4 : (851 / 400 : ℝ) ^ 4 ≤ v ^ 4 := pow_le_pow_left₀ (by norm_num) hv 4
  have h_v5 : (851 / 400 : ℝ) ^ 5 ≤ v ^ 5 := pow_le_pow_left₀ (by norm_num) hv 5
  have h_mono :
      (39 / 10 : ℝ) ≤ 2 + v / 4 + v ^ 2 / 6 + v ^ 3 / 24 + v ^ 4 / 120 + v ^ 5 / 720 := by
    linarith
  have h_mul :
      (39 / 10 : ℝ) * v ≤
        v * (2 + v / 4 + v ^ 2 / 6 + v ^ 3 / 24 + v ^ 4 / 120 + v ^ 5 / 720) := by
    nlinarith
  have h_id :
      1 + v + v ^ 2 / 2 + v ^ 3 / 6 + v ^ 4 / 24 + v ^ 5 / 120 + v ^ 6 / 720 =
        (v / 2 - 1) ^ 2 +
          v * (2 + v / 4 + v ^ 2 / 6 + v ^ 3 / 24 + v ^ 4 / 120 + v ^ 5 / 720) := by
    ring
  linarith

/-- For `x ≥ 5000`, `(Real.log x) ^ 2 ≤ (20 / 19) * Real.sqrt x`. -/
lemma sq_log_le_twenty_nineteenths_sqrt {x : ℝ} (hx : 5000 ≤ x) :
    (Real.log x) ^ 2 ≤ (20 / 19 : ℝ) * Real.sqrt x := by
  have hL : (851 / 100 : ℝ) ≤ Real.log x := log_ge_851_div_100 hx
  have hv : (851 / 400 : ℝ) ≤ Real.log x / 4 := by linarith
  have hexp := exp_ge_thirty_nine_tenths_mul hv
  have h_exp_sq : (Real.exp (Real.log x / 4)) ^ 2 = Real.sqrt x := by
    rw [sq, ← Real.exp_add]
    have h_half : Real.log x / 4 + Real.log x / 4 = Real.log (Real.sqrt x) := by
      rw [Real.log_sqrt (by linarith)]
      ring
    rw [h_half, Real.exp_log (Real.sqrt_pos.mpr (by linarith))]
  have h_lhs_nonneg : 0 ≤ (39 / 10 : ℝ) * (Real.log x / 4) := by linarith
  have h_sq_le : ((39 / 10 : ℝ) * (Real.log x / 4)) ^ 2 ≤ (Real.exp (Real.log x / 4)) ^ 2 :=
    pow_le_pow_left₀ h_lhs_nonneg hexp 2
  rw [h_exp_sq] at h_sq_le
  nlinarith

/-- Helper bounds on `Real.sqrt (x + h)`, `(x + h) ^ (3 / 2 : ℝ)`, and `(x + h) ^ (3 / 4 : ℝ)`. -/
lemma rpow_xh_bounds {x h S L : ℝ} (hx : 5000 ≤ x) (hS : 70 ≤ S) (hS_sq : S ^ 2 = x)
    (hL_sq : (7242 / 100 : ℝ) ≤ L ^ 2) (hh_def : h = (7 / 20 : ℝ) * S * L ^ 2)
    (hh_le_x : h ≤ (7 / 19 : ℝ) * x) :
    S ≤ Real.sqrt (x + h) ∧
      Real.sqrt (x + h) ≤ (34 / 29 : ℝ) * S ∧
      (x + h) ^ (3 / 2 : ℝ) ≤ (161 / 100 : ℝ) * S ^ 3 ∧
      (x + h) ^ (3 / 4 : ℝ) ≤ (26 / 171 : ℝ) * S ^ 2 := by
  have hS_pos : 0 < S := by linarith
  have hh_ge : 1600 ≤ h := by
    rw [hh_def]
    nlinarith
  have hx_add_h_le' : x + h ≤ (26 / 19 : ℝ) * S ^ 2 := by linarith
  have hx_add_h_le : x + h ≤ ((34 / 29 : ℝ) * S) ^ 2 := by nlinarith
  have h_sqrt_ge : S ≤ Real.sqrt (x + h) := by
    have h1 : S ^ 2 ≤ x + h := by linarith
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq hS_pos.le] at h2
  have h_sqrt_xh : Real.sqrt (x + h) ≤ (34 / 29 : ℝ) * S := by
    have h1 := Real.sqrt_le_sqrt hx_add_h_le
    rwa [Real.sqrt_sq (by positivity)] at h1
  have h_rpow_32 : (x + h) ^ (3 / 2 : ℝ) ≤ (161 / 100 : ℝ) * S ^ 3 := by
    have h_split : (x + h) ^ (3 / 2 : ℝ) = (x + h) * Real.sqrt (x + h) := by
      have h_eq : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
      rw [h_eq, Real.rpow_add (by linarith), Real.rpow_one, ← Real.sqrt_eq_rpow]
    have h_sqrt_nonneg : 0 ≤ Real.sqrt (x + h) := Real.sqrt_nonneg _
    rw [h_split]
    nlinarith
  have h_rpow_34 : (x + h) ^ (3 / 4 : ℝ) ≤ (26 / 171 : ℝ) * S ^ 2 := by
    have h6561 : (9 : ℝ) ^ (4 : ℝ) ≤ x + h := by norm_num; linarith
    have h9_le : (9 : ℝ) ≤ (x + h) ^ (1 / 4 : ℝ) := by
      have h1 := Real.rpow_le_rpow (by positivity) h6561 (by norm_num : (0 : ℝ) ≤ 1 / 4)
      rw [← Real.rpow_mul (by norm_num)] at h1
      norm_num at h1
      exact h1
    have h_prod : (x + h) ^ (3 / 4 : ℝ) * (x + h) ^ (1 / 4 : ℝ) = x + h := by
      rw [← Real.rpow_add (by linarith)]
      norm_num
    have h_nonneg : 0 ≤ (x + h) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (by linarith) _
    nlinarith
  exact ⟨h_sqrt_ge, h_sqrt_xh, h_rpow_32, h_rpow_34⟩

/-- Helper bounds on `Real.log T` and `Real.log 6`. -/
lemma log_T_and_six_bounds {L S T : ℝ}
    (hL : (851 / 100 : ℝ) ≤ L) (hS_pos : 0 < S) (hS_log : Real.log S = L / 2)
    (h6_le_T : 6 ≤ T) (hT_def : T = (3 / 2 : ℝ) * S / L) :
    0 ≤ Real.log T ∧ Real.log T ≤ L / 2 - 429 / 250 ∧ (89 / 50 : ℝ) ≤ Real.log 6 := by
  have hL_pos : 0 < L := by linarith
  have h_logL : (533 / 250 : ℝ) ≤ Real.log L := by
    have hpow : (2 : ℝ) ^ (40 : ℕ) ≤ L ^ (13 : ℕ) := by
      have h1 : (2 : ℝ) ^ (40 : ℕ) ≤ (851 / 100 : ℝ) ^ (13 : ℕ) := by norm_num
      have h2 : (851 / 100 : ℝ) ^ (13 : ℕ) ≤ L ^ (13 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) hL 13
      exact h1.trans h2
    have hlog := Real.log_le_log (by positivity) hpow
    rw [Real.log_pow, Real.log_pow] at hlog
    have hlog2 := Real.log_two_gt_d9
    push_cast at hlog
    linarith
  have h_log32 : Real.log (3 / 2 : ℝ) ≤ 52 / 125 := by
    have hpow : ((3 / 2 : ℝ) ^ (5 : ℕ)) ≤ (2 : ℝ) ^ (3 : ℕ) := by norm_num
    have hlog := Real.log_le_log (by positivity) hpow
    rw [Real.log_pow, Real.log_pow] at hlog
    have hlog2 := Real.log_two_lt_d9
    push_cast at hlog
    linarith
  have h_logT_eq : Real.log T = Real.log (3 / 2 : ℝ) + Real.log S - Real.log L := by
    rw [hT_def, Real.log_div (by positivity) hL_pos.ne',
      Real.log_mul (by norm_num) hS_pos.ne']
  have h_logT_le : Real.log T ≤ L / 2 - 429 / 250 := by linarith
  have h_logT_nonneg : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have h_log6_ge : (89 / 50 : ℝ) ≤ Real.log 6 := by
    have hpow : (2 : ℝ) ^ (18 : ℕ) ≤ (6 : ℝ) ^ (7 : ℕ) := by norm_num
    have hlog := Real.log_le_log (by positivity) hpow
    rw [Real.log_pow, Real.log_pow] at hlog
    have hlog2 := Real.log_two_gt_d9
    push_cast at hlog
    linarith
  exact ⟨h_logT_nonneg, h_logT_le, h_log6_ge⟩

/-- Helper bound for Term 2: `Real.log (2 * Real.pi) ≤ (1 / 500) * S * L ^ 2`. -/
lemma term2_bound {S L : ℝ} (hS : 70 ≤ S) (hL_sq : (7242 / 100 : ℝ) ≤ L ^ 2) :
    Real.log (2 * Real.pi) ≤ (1 / 500 : ℝ) * S * L ^ 2 := by
  have hpi : 2 * Real.pi ≤ 8 := by have := Real.pi_le_four; linarith
  have hlog_2pi : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hSL : 4000 ≤ S * L ^ 2 := by nlinarith
  linarith

/-- Helper bound for Term 3 + Term 4 combined. -/
lemma term3_add_term4_bound {x h S L T : ℝ} (hS_pos : 0 < S) (hL : (851 / 100 : ℝ) ≤ L)
    (hL_sq : (7242 / 100 : ℝ) ≤ L ^ 2) (hh_pos : 0 < h) (hT_pos : 0 < T)
    (hh_def : h = (7 / 20 : ℝ) * S * L ^ 2) (hT_def : T = (3 / 2 : ℝ) * S / L)
    (h_sqrt_ge : S ≤ Real.sqrt (x + h))
    (h_sqrt_xh : Real.sqrt (x + h) ≤ (34 / 29 : ℝ) * S)
    (h_rpow_32 : (x + h) ^ (3 / 2 : ℝ) ≤ (161 / 100 : ℝ) * S ^ 3)
    (h_logT_nonneg : 0 ≤ Real.log T) (h_logT_le : Real.log T ≤ L / 2 - 429 / 250)
    (h_log6_ge : (89 / 50 : ℝ) ≤ Real.log 6) :
    Real.sqrt (x + h) *
        ((16 / 5 : ℝ) / 2 * (Real.log T) ^ 2 + ((16 / 5 : ℝ) + (11 / 5 : ℝ)) * Real.log T +
          (11 / 5 : ℝ) + (0 : ℝ) / 6 -
          (16 / 5 : ℝ) / 2 * (Real.log 6) ^ 2 - (11 / 5 : ℝ) * Real.log 6) +
      (2 * (x + h) ^ (3 / 2 : ℝ) / h) *
        ((2 * (16 / 5 : ℝ) * Real.log T + 2 * (16 / 5 : ℝ) + 2 * (11 / 5 : ℝ)) / T +
          2 * (0 : ℝ) / T ^ 2) ≤
      (59 / 100 : ℝ) * S * L ^ 2 := by
  have hL_pos : 0 < L := by linarith
  -- Bound on Term 3
  have h_sq_T : (Real.log T) ^ 2 ≤ (L / 2 - 429 / 250) ^ 2 :=
    sq_le_sq' (by linarith) h_logT_le
  have h_sq_6 : (89 / 50 : ℝ) ^ 2 ≤ (Real.log 6) ^ 2 :=
    sq_le_sq' (by linarith) h_log6_ge
  have h_bracket3 :
      (16 / 5 : ℝ) / 2 * (Real.log T) ^ 2 + ((16 / 5 : ℝ) + (11 / 5 : ℝ)) * Real.log T +
          (11 / 5 : ℝ) + (0 : ℝ) / 6 -
          (16 / 5 : ℝ) / 2 * (Real.log 6) ^ 2 - (11 / 5 : ℝ) * Real.log 6 ≤
        (2 / 5 : ℝ) * L ^ 2 - 23 / 2 := by
    nlinarith
  have h_term3 :
      Real.sqrt (x + h) *
          ((16 / 5 : ℝ) / 2 * (Real.log T) ^ 2 + ((16 / 5 : ℝ) + (11 / 5 : ℝ)) * Real.log T +
            (11 / 5 : ℝ) + (0 : ℝ) / 6 -
            (16 / 5 : ℝ) / 2 * (Real.log 6) ^ 2 - (11 / 5 : ℝ) * Real.log 6) ≤
        (68 / 145 : ℝ) * S * L ^ 2 - (23 / 2 : ℝ) * S := by
    have h1 := mul_le_mul_of_nonneg_left h_bracket3 (Real.sqrt_nonneg (x + h))
    have h2 : Real.sqrt (x + h) * ((2 / 5 : ℝ) * L ^ 2) ≤
        ((34 / 29 : ℝ) * S) * ((2 / 5 : ℝ) * L ^ 2) :=
      mul_le_mul_of_nonneg_right h_sqrt_xh (by positivity)
    linarith
  -- Bound on Term 4
  have h_term4 :
      (2 * (x + h) ^ (3 / 2 : ℝ) / h) *
          ((2 * (16 / 5 : ℝ) * Real.log T + 2 * (16 / 5 : ℝ) + 2 * (11 / 5 : ℝ)) / T +
            2 * (0 : ℝ) / T ^ 2) ≤
        (99 / 5 : ℝ) * S := by
    rw [mul_zero, zero_div, add_zero, div_mul_div_comm]
    rw [div_le_iff₀ (mul_pos hh_pos hT_pos)]
    have h_hT : h * T = (21 / 40 : ℝ) * S ^ 2 * L := by
      rw [hh_def, hT_def]
      field_simp [hL_pos.ne']
      ring
    rw [h_hT]
    have h_num1 : 2 * (x + h) ^ (3 / 2 : ℝ) ≤ (161 / 50 : ℝ) * S ^ 3 := by linarith
    have h_num2 : 2 * (16 / 5 : ℝ) * Real.log T + 2 * (16 / 5 : ℝ) + 2 * (11 / 5 : ℝ) ≤
        (16 / 5 : ℝ) * L := by linarith
    have h_prod :
        2 * (x + h) ^ (3 / 2 : ℝ) *
            (2 * (16 / 5 : ℝ) * Real.log T + 2 * (16 / 5 : ℝ) + 2 * (11 / 5 : ℝ)) ≤
          ((161 / 50 : ℝ) * S ^ 3) * ((16 / 5 : ℝ) * L) :=
      mul_le_mul h_num1 h_num2 (by positivity) (by positivity)
    have h_rhs :
        ((161 / 50 : ℝ) * S ^ 3) * ((16 / 5 : ℝ) * L) ≤
          (99 / 5 : ℝ) * S * ((21 / 40 : ℝ) * S ^ 2 * L) := by
      have h_diff :
          (99 / 5 : ℝ) * S * ((21 / 40 : ℝ) * S ^ 2 * L) -
              ((161 / 50 : ℝ) * S ^ 3) * ((16 / 5 : ℝ) * L) =
            (91 / 1000 : ℝ) * S ^ 3 * L := by ring
      have : 0 ≤ (91 / 1000 : ℝ) * S ^ 3 * L := by positivity
      linarith
    linarith
  have hS_le_SL2 : (83 / 10 : ℝ) * S ≤ (59 / 100 - 68 / 145 : ℝ) * S * L ^ 2 := by
    nlinarith
  linarith

/-- Helper bound for Term 5: left-vertical line `Re s = -1 / 4` contribution. -/
lemma term5_bound {x h S L : ℝ} (hS_pos : 0 < S) (hL_pos : 0 < L)
    (hL_sq : (7242 / 100 : ℝ) ≤ L ^ 2) (hh_pos : 0 < h)
    (hh_def : h = (7 / 20 : ℝ) * S * L ^ 2)
    (h_rpow_34 : (x + h) ^ (3 / 4 : ℝ) ≤ (26 / 171 : ℝ) * S ^ 2) :
    32 * (2 * (1 : ℝ) + (85 : ℝ)) / (Real.pi * h) * (x + h) ^ (3 / 4 : ℝ) ≤
      (8 / 100 : ℝ) * S * L ^ 2 := by
  rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos Real.pi_pos hh_pos)]
  have hpi_gt : (3 : ℝ) ≤ Real.pi := by
    have h_sin : (1 / 2 : ℝ) < Real.pi / 6 := by
      rw [← Real.sin_pi_div_six]
      exact Real.sin_lt (by positivity)
    linarith
  have h_num : 32 * (2 * (1 : ℝ) + 85) * (x + h) ^ (3 / 4 : ℝ) ≤ (24128 / 57 : ℝ) * S ^ 2 := by
    linarith
  have h1 : (3 : ℝ) * h ≤ Real.pi * h :=
    mul_le_mul_of_nonneg_right hpi_gt hh_pos.le
  have h2 : (7242 / 100 : ℝ) ^ 2 ≤ (L ^ 2) ^ 2 :=
    sq_le_sq' (by linarith) hL_sq
  have h3 : (24128 / 57 : ℝ) * S ^ 2 ≤
      (8 / 100 : ℝ) * S * L ^ 2 * ((3 : ℝ) * h) := by
    rw [hh_def]
    have h_diff :
        (8 / 100 : ℝ) * S * L ^ 2 * ((3 : ℝ) * ((7 / 20 : ℝ) * S * L ^ 2)) -
            (24128 / 57 : ℝ) * S ^ 2 =
          S ^ 2 * ((21 / 250 : ℝ) * (L ^ 2) ^ 2 - 24128 / 57) := by ring
    have : 0 ≤ S ^ 2 * ((21 / 250 : ℝ) * (L ^ 2) ^ 2 - 24128 / 57) := by
      have : 0 ≤ (21 / 250 : ℝ) * (L ^ 2) ^ 2 - 24128 / 57 := by linarith
      positivity
    linarith
  have h4 :
      (8 / 100 : ℝ) * S * L ^ 2 * ((3 : ℝ) * h) ≤
        (8 / 100 : ℝ) * S * L ^ 2 * (Real.pi * h) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  linarith

/-- **Main Large-`x` Inequality (`x ≥ 5000`)**:
For all `x ≥ 5000`, the explicit parameters `h = (7 / 20) * √x * (log x)^2` and
`T = (3 / 2) * √x / log x` satisfy `1 ≤ x - h`, `0 < h`, `6 ≤ T`, and the full explicit bound
is at most `(7 / 8) * √x * (log x)^2`. -/
theorem explicit_rhs_le_seven_eighths_of_five_thousand_le
    {x : ℝ} (hx : 5000 ≤ x) :
    let h := (7 / 20 : ℝ) * Real.sqrt x * (Real.log x) ^ 2
    let T := (3 / 2 : ℝ) * Real.sqrt x / Real.log x
    let a_rvM := (16 / 5 : ℝ)
    let C := (11 / 5 : ℝ)
    let D := (0 : ℝ)
    let A := (1 : ℝ)
    let B := (85 : ℝ)
    (1 ≤ x - h ∧ 0 < h ∧ 6 ≤ T) ∧
      h / 2 + Real.log (2 * Real.pi) +
        Real.sqrt (x + h) *
          (a_rvM / 2 * (Real.log T) ^ 2 + (a_rvM + C) * Real.log T + C + D / 6 -
            a_rvM / 2 * (Real.log 6) ^ 2 - C * Real.log 6) +
        (2 * (x + h) ^ (3 / 2 : ℝ) / h) *
          ((2 * a_rvM * Real.log T + 2 * a_rvM + 2 * C) / T + 2 * D / T ^ 2) +
        32 * (2 * A + B) / (Real.pi * h) * (x + h) ^ (3 / 4 : ℝ) ≤
      (7 / 8 : ℝ) * Real.sqrt x * (Real.log x) ^ 2 := by
  intro h T a_rvM C D A B
  set L : ℝ := Real.log x
  set S : ℝ := Real.sqrt x
  have hL : (851 / 100 : ℝ) ≤ L := log_ge_851_div_100 hx
  have hL_pos : 0 < L := by linarith
  have hL_sq : (7242 / 100 : ℝ) ≤ L ^ 2 := by nlinarith
  have hS : (70 : ℝ) ≤ S := sqrt_ge_seventy hx
  have hS_pos : 0 < S := by linarith
  have hS_sq : S ^ 2 = x := Real.sq_sqrt (by linarith)
  have hL2_le_S : L ^ 2 ≤ (20 / 19 : ℝ) * S := sq_log_le_twenty_nineteenths_sqrt hx
  have hh_def : h = (7 / 20 : ℝ) * S * L ^ 2 := rfl
  have hT_def : T = (3 / 2 : ℝ) * S / L := rfl
  have hh_pos : 0 < h := by rw [hh_def]; positivity
  have hh_le_x : h ≤ (7 / 19 : ℝ) * x := by
    calc h = (7 / 20 : ℝ) * S * L ^ 2 := hh_def
      _ ≤ (7 / 20 : ℝ) * S * ((20 / 19 : ℝ) * S) := by nlinarith
      _ = (7 / 19 : ℝ) * S ^ 2 := by ring
      _ = (7 / 19 : ℝ) * x := by rw [hS_sq]
  have hx_sub_h : 1 ≤ x - h := by linarith
  have h6_le_T : 6 ≤ T := by
    rw [hT_def, le_div_iff₀ hL_pos]
    nlinarith
  have hT_pos : 0 < T := by linarith
  refine ⟨⟨hx_sub_h, hh_pos, h6_le_T⟩, ?_⟩
  obtain ⟨h_sqrt_ge, h_sqrt_xh, h_rpow_32, h_rpow_34⟩ :=
    rpow_xh_bounds hx hS hS_sq hL_sq hh_def hh_le_x
  obtain ⟨h_logT_nonneg, h_logT_le, h_log6_ge⟩ :=
    log_T_and_six_bounds hL hS_pos (Real.log_sqrt (by linarith)) h6_le_T hT_def
  have h_term1 : h / 2 = (7 / 40 : ℝ) * S * L ^ 2 := by rw [hh_def]; ring
  have h_term2 : Real.log (2 * Real.pi) ≤ (1 / 500 : ℝ) * S * L ^ 2 :=
    term2_bound hS hL_sq
  have h_term34 := term3_add_term4_bound hS_pos hL hL_sq hh_pos hT_pos hh_def hT_def
    h_sqrt_ge h_sqrt_xh h_rpow_32 h_logT_nonneg h_logT_le h_log6_ge
  have h_term5 := term5_bound hS_pos hL_pos hL_sq hh_pos hh_def h_rpow_34
  dsimp [a_rvM, C, D, A, B]
  linarith

end ConjectureMachines.Semantics.Riemann.ExplicitLarge
