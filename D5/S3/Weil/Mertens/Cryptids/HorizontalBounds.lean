/- GID: D5/S3/Weil/Mertens/Cryptids/HorizontalBounds
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/Cryptids/HorizontalBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original Cryptids HorizontalBounds analytic source for the RH Chebyshev bound. -/

/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in
  docs/reports/licenses/cryptids-LICENSE.txt.
Source: https://github.com/google-deepmind/cryptids/blob/e5f59ed70d1549a61ef8873a6fbae9268fdbd557/Cryptids/Semantics/Riemann/HorizontalBounds.lean
Routing adaptations: ordinary D5 modules, redirected imports, and declaration-boundary splitting.
The original declaration namespaces, statements, and mathematical proof text are retained.
Retirement: when this repository's lake-manifest.json Mathlib revision provides an equivalent
RH-only real-x Chebyshev psi estimate for x >= 5000, replace the target with that declaration
and delete the transplanted declarations no longer in its live dependency closure.
-/

import D5.S3.Weil.Mertens.Cryptids.HorizontalBounds.Integral

/-! Original HorizontalBounds analytic supplier for the RH Chebyshev estimate. -/

namespace ConjectureMachines.Semantics.Riemann.HorizontalBounds

open Complex Filter MeasureTheory Set Asymptotics Metric MeromorphicOn ComplexConjugate
open scoped Real Topology ArithmeticFunction LSeries.notation

/-- **Existential `O((log U) ^ 5)` Horizontal Bound at Arbitrarily Large Zero-Free Heights**:
For every `T ≥ 6`, under `RiemannHypothesis`, there exists a constant `C_h ≥ 0` such that
for every `U₀ ≥ T`, there exists a zero-free height `U ≥ U₀` (in fact `U ∈ Set.Icc U₀ (U₀ + 1)`)
such that:
1. Every `ρ ∈ nontrivialZetaZerosUpTo U` satisfies `|ρ.im| < U`,
2. Every `σ ∈ Set.Icc (-1 / 4 : ℝ) 2` satisfies
   `‖-deriv riemannZeta (σ + U * I) / riemannZeta (σ + U * I)‖ ≤ C_h * (Real.log U) ^ 5`,
3. Every `σ ∈ Set.Icc (-1 / 4 : ℝ) 2` satisfies
   `‖-deriv riemannZeta (σ - U * I) / riemannZeta (σ - U * I)‖ ≤ C_h * (Real.log U) ^ 5`. -/
theorem exists_zero_free_height_with_log_pow_five_bound
    (hRH : RiemannHypothesis) {T : ℝ} (hT : 6 ≤ T) :
    ∃ C_h : ℝ, 0 ≤ C_h ∧ ∀ U₀ ≥ T, ∃ U ≥ U₀,
      (∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) ∧
      (∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
        ‖-deriv riemannZeta ((σ : ℂ) + (U : ℂ) * I) /
          riemannZeta ((σ : ℂ) + (U : ℂ) * I)‖ ≤ C_h * (Real.log U) ^ 5) ∧
      (∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
        ‖-deriv riemannZeta ((σ : ℂ) - (U : ℂ) * I) /
          riemannZeta ((σ : ℂ) - (U : ℂ) * I)‖ ≤ C_h * (Real.log U) ^ 5) := by
  let C_h : ℝ := 3 * (2048 * 628 ^ 4 + 1) + 14
  refine ⟨C_h, by dsimp [C_h]; norm_num, ?_⟩
  intro U₀ hU₀
  have hU₀_ge6 : 6 ≤ U₀ := hT.trans hU₀
  obtain ⟨U, hU_mem, Δ, hΔ_pos, _hΔ_le, hΔ_lb, hgap, h_horiz⟩ :=
    exists_zero_free_height_with_horizontal_bounds hRH (T := U₀) (by linarith)
  have hU_ge_U₀ : U₀ ≤ U := hU_mem.1
  have hU_ge6 : 6 ≤ U := hU₀_ge6.trans hU_ge_U₀
  have hU_pos : 0 < U := by linarith
  have h_logU_ge_one : 1 ≤ Real.log U := by
    have h_exp : Real.exp 1 ≤ U := by linarith [Real.exp_one_lt_d9]
    have h_log := Real.log_le_log (Real.exp_pos 1) h_exp
    rwa [Real.log_exp] at h_log
  have h_logU_pos : 0 < Real.log U := zero_lt_one.trans_le h_logU_ge_one
  have h_log_U₀_add10 : Real.log (U₀ + 10) ≤ 2 * Real.log U := by
    have h_le_sq : U₀ + 10 ≤ U ^ 2 := by nlinarith
    calc
      Real.log (U₀ + 10) ≤ Real.log (U ^ 2) :=
        Real.log_le_log (by linarith) h_le_sq
      _ = 2 * Real.log U := by rw [Real.log_pow]; push_cast; ring
  have h_log_14 : Real.log (14 * (1 + U)) ≤ 3 * Real.log U := by
    have h_le_cube : 14 * (1 + U) ≤ U ^ 3 := by
      have hU2 : 36 ≤ U ^ 2 := by nlinarith
      have hU3 : U ^ 3 = U ^ 2 * U := by ring
      nlinarith
    calc
      Real.log (14 * (1 + U)) ≤ Real.log (U ^ 3) :=
        Real.log_le_log (by positivity) h_le_cube
      _ = 3 * Real.log U := by rw [Real.log_pow]; push_cast; ring
  have h_inv_Δ : 1 / Δ ≤ 628 * Real.log U := by
    have h_den_pos : 0 < 314 * Real.log (U₀ + 10) := by
      have : 1 < U₀ + 10 := by linarith
      exact mul_pos (by norm_num) (Real.log_pos this)
    have h_prod : 1 ≤ Δ * (314 * Real.log (U₀ + 10)) :=
      (div_le_iff₀ h_den_pos).mp hΔ_lb
    have h1 : 1 / Δ ≤ 314 * Real.log (U₀ + 10) := by
      rw [div_le_iff₀ hΔ_pos]
      linarith
    linarith
  have h_inv_Δ4 : 2048 / Δ ^ 4 + 1 ≤ (2048 * 628 ^ 4 + 1) * (Real.log U) ^ 4 := by
    have h_pow4 : (1 / Δ) ^ 4 ≤ (628 * Real.log U) ^ 4 :=
      pow_le_pow_left₀ (by positivity) h_inv_Δ 4
    have h_div_eq : 2048 / Δ ^ 4 = 2048 * (1 / Δ) ^ 4 := by ring
    have h_one_le : (1 : ℝ) ≤ (Real.log U) ^ 4 := one_le_pow₀ h_logU_ge_one
    have h_rhs_eq :
        2048 * (628 * Real.log U) ^ 4 + (Real.log U) ^ 4 =
          (2048 * 628 ^ 4 + 1) * (Real.log U) ^ 4 := by ring
    linarith
  have h_main_bound :
      (2048 / Δ ^ 4 + 1) * Real.log (14 * (1 + U)) + 14 ≤ C_h * (Real.log U) ^ 5 := by
    have h_mul :
        (2048 / Δ ^ 4 + 1) * Real.log (14 * (1 + U)) ≤
          ((2048 * 628 ^ 4 + 1) * (Real.log U) ^ 4) * (3 * Real.log U) :=
      mul_le_mul h_inv_Δ4 h_log_14 (Real.log_nonneg (by linarith)) (by positivity)
    have h_one_le5 : (1 : ℝ) ≤ (Real.log U) ^ 5 := one_le_pow₀ h_logU_ge_one
    have h_alg :
        ((2048 * 628 ^ 4 + 1) * (Real.log U) ^ 4) * (3 * Real.log U) + 14 * (Real.log U) ^ 5 =
          C_h * (Real.log U) ^ 5 := by
      dsimp [C_h]
      ring
    linarith
  refine ⟨U, hU_ge_U₀, ?_, ?_, ?_⟩
  · intro ρ hρ
    obtain ⟨h_nt, him_le⟩ := mem_nontrivialZetaZerosUpTo.mp hρ
    have hre : ρ.re = 1 / 2 := re_eq_half_of_isNontrivialZetaZero hRH h_nt
    have h_abs_gap := (hgap ρ h_nt.1 hre).1
    have h_ne : |ρ.im| ≠ U := by
      intro h_eq
      rw [h_eq, sub_self, abs_zero] at h_abs_gap
      linarith
    exact lt_of_le_of_ne him_le h_ne
  · intro σ hσ
    rw [neg_div, norm_neg]
    exact (h_horiz σ hσ).1.trans h_main_bound
  · intro σ hσ
    rw [neg_div, norm_neg]
    exact (h_horiz σ hσ).2.trans h_main_bound

end ConjectureMachines.Semantics.Riemann.HorizontalBounds
