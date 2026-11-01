/- GID: D5/S3/Weil/Mertens/Cryptids/WeightedStieltjes/Integral
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/Cryptids/WeightedStieltjes/Integral
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original Cryptids WeightedStieltjes analytic source for the RH Chebyshev bound. -/

/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in
  docs/reports/licenses/cryptids-LICENSE.txt.
Source: https://github.com/google-deepmind/cryptids/blob/e5f59ed70d1549a61ef8873a6fbae9268fdbd557/Cryptids/Semantics/Riemann/WeightedStieltjes.lean
Routing adaptations: ordinary D5 modules, redirected imports, and declaration-boundary splitting.
The original declaration namespaces, statements, and mathematical proof text are retained.
Retirement: when this repository's lake-manifest.json Mathlib revision provides an equivalent
RH-only real-x Chebyshev psi estimate for x >= 5000, replace the target with that declaration
and delete the transplanted declarations no longer in its live dependency closure.
-/

import D5.S3.Weil.Mertens.Cryptids.WeightedStieltjes.Foundation

/-! Original WeightedStieltjes analytic supplier for the RH Chebyshev estimate. -/

namespace ConjectureMachines.Semantics.Riemann.WeightedStieltjes

open Complex Finset Filter MeasureTheory Set Asymptotics Topology
open scoped Real Topology Interval

open Real

open scoped ArithmeticFunction.vonMangoldt LSeries.notation

/-- **Smoothed Perron Formula for `y ≥ 1`**:
When `1 ≤ y` and `0 < c`, the vertical integral of `smoothedPerronKernel y` equals `2 * π * (y -
1)`. -/
theorem integral_smoothedPerronKernel_eq_of_ge_one {y c : ℝ} (hy1 : 1 ≤ y) (hc : 0 < c) :
    (∫ t : ℝ, smoothedPerronKernel y ((c : ℂ) + (t : ℂ) * I)) = 2 * π * ((y : ℂ) - 1) := by
  have hy : 0 < y := zero_lt_one.trans_le hy1
  have hc0_pos : (0 : ℝ) < 1 / 2 := by norm_num
  have hc0_lt1 : (1 / 2 : ℝ) < 1 := by norm_num
  rw [integral_smoothedPerronKernel_eq_of_pos hy hc0_pos hc]
  obtain ⟨h_int_c0, h_eval_c0⟩ := integrable_and_integral_perronAux_of_mem_Ioo hy hc0_pos hc0_lt1
  suffices h_zero : (∫ t : ℝ, perronAux y (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) = 0 by
    linear_combination -h_eval_c0 + h_zero
  have h_shift : ∀ C : ℝ, C < -1 →
      (∫ t : ℝ, perronAux y (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) =
        ∫ t : ℝ, perronAux y ((C : ℂ) + (t : ℂ) * I) := by
    intro C hC
    let U : Set ℂ := {s : ℂ | s.re < 1}
    have hU : IsOpen U := isOpen_lt Complex.continuous_re continuous_const
    have hF : DifferentiableOn ℂ (perronAux y) U := differentiableOn_perronAux hy
    let M : ℝ := max (y ^ (C + 1)) (y ^ ((1 / 2 : ℝ) + 1))
    refine integral_vertical_eq_of_differentiableOn_strip hU hF
      (fun σ hσ t ↦ ?_) (integrable_perronAux_of_lt_neg_one hy1 hC) h_int_c0
      (B := fun T : ℝ ↦ (M + y + 2) * (T ^ 2)⁻¹) ?_ ?_ ?_
    · change ((σ : ℂ) + (t : ℂ) * I).re < 1
      rw [re_ofReal_add_ofReal_mul_I]
      have h_max : max C (1 / 2) < 1 := max_lt (by linarith) hc0_lt1
      exact lt_of_le_of_lt hσ.2 h_max
    · have h_tendsto : Tendsto (fun T : ℝ ↦ (T ^ 2)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
      simpa using h_tendsto.const_mul (M + y + 2)
    · filter_upwards [eventually_gt_atTop 0] with T hT σ hσ
      have h_le := norm_perronAux_horizontal_le hy (c := σ) hT.ne'
      have h_yσ : y ^ (σ + 1) ≤ M := rpow_add_one_le_max_of_mem_uIcc hy hσ
      exact h_le.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    · filter_upwards [eventually_gt_atTop 0] with T hT σ hσ
      have h_le := norm_perronAux_horizontal_le hy (c := σ) (neg_ne_zero.mpr hT.ne')
      rw [neg_sq] at h_le
      have h_yσ : y ^ (σ + 1) ≤ M := rpow_add_one_le_max_of_mem_uIcc hy hσ
      exact h_le.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have h_bound : ∀ u : ℝ, 0 < u →
      ‖∫ t : ℝ, perronAux y (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ (y + 3) * (π / u) := by
    intro u hu
    have hC : -(u + 1) < -1 := by linarith
    rw [h_shift (-(u + 1)) hC]
    have hC1 : -(u + 1) + 1 = -u := by ring
    have h_neg_u_ne : -(u + 1) + 1 ≠ 0 := by linarith
    calc ‖∫ t : ℝ, perronAux y (((-(u + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖
        ≤ ∫ t : ℝ, ‖perronAux y (((-(u + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, (y + 3) * ((-(u + 1) + 1) ^ 2 + t ^ 2)⁻¹ := by
          refine integral_mono (integrable_perronAux_of_lt_neg_one hy1 hC).norm
            ((integrable_inv_sq_add_sq h_neg_u_ne).const_mul (y + 3))
            (norm_perronAux_vertical_le_of_lt_neg_one hy1 hC)
      _ = (y + 3) * (π / |-(u + 1) + 1|) := by
          rw [integral_const_mul, integral_inv_sq_add_sq h_neg_u_ne]
      _ = (y + 3) * (π / u) := by
          rw [hC1, abs_neg, abs_of_pos hu]
  have h_tendsto : Tendsto (fun u : ℝ ↦ (y + 3) * (π / u)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.const_mul π).const_mul (y + 3)
  have h_norm_le : ‖∫ t : ℝ, perronAux y (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ 0 := by
    refine ge_of_tendsto h_tendsto ?_
    filter_upwards [eventually_gt_atTop 0] with u hu
    exact h_bound u hu
  exact norm_le_zero_iff.mp h_norm_le

/-- **Combined Smoothed Perron Kernel Formula**:
For all `0 < y` and `0 < c`,
`((2 * π : ℂ)⁻¹) * ∫ t : ℝ, y ^ (c + 1 + t * I) / ((c + t * I) * (c + 1 + t * I)) = max (y - 1) 0`.
-/
theorem smoothed_perron_kernel_eval {y c : ℝ} (hy : 0 < y) (hc : 0 < c) :
    (2 * (π : ℂ))⁻¹ * (∫ t : ℝ, smoothedPerronKernel y ((c : ℂ) + (t : ℂ) * I)) =
      ((max (y - 1) 0 : ℝ) : ℂ) := by
  have hpi : (2 * (π : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  rcases le_or_gt y 1 with hy1 | hy1
  · rw [integral_smoothedPerronKernel_eq_zero_of_le_one hy hy1 hc, mul_zero,
      max_eq_right (by linarith : y - 1 ≤ 0), Complex.ofReal_zero]
  · rw [integral_smoothedPerronKernel_eq_of_ge_one hy1.le hc,
      max_eq_left (by linarith : 0 ≤ y - 1), Complex.ofReal_sub, Complex.ofReal_one]
    field_simp [hpi]

/-!
# Section 3: Smoothed Perron Formula for `ψ₁(x) = ∑_{n ≤ x} Λ(n) * (x - n)`
-/

/-- For `0 < x`, `n ≠ 0`, and any `s : ℂ`, multiplying `LSeries.term f s n` by
`smoothedPerronKernel x s` rescales the argument of `smoothedPerronKernel` to `x / n`. -/
lemma term_mul_smoothedPerronKernel_of_ne_zero {f : ℕ → ℂ} {x : ℝ} (hx : 0 < x)
    {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    LSeries.term f s n * smoothedPerronKernel x s =
      (f n * (n : ℂ)) * smoothedPerronKernel (x / n) s := by
  have hn_c : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h_div : (((x / n : ℝ) : ℂ)) ^ (s + 1) = (x : ℂ) ^ (s + 1) / ((n : ℂ) ^ s * (n : ℂ)) := by
    rw [Complex.ofReal_div, Complex.ofReal_natCast,
      ← Complex.ofReal_natCast n,
      Complex.div_cpow_ofReal_nonneg hx.le (Nat.cast_nonneg n) (s + 1),
      Complex.ofReal_natCast, Complex.cpow_add _ _ hn_c, Complex.cpow_one]
  unfold smoothedPerronKernel
  rw [LSeries.term_of_ne_zero hn, h_div]
  calc (f n / (n : ℂ) ^ s) * ((x : ℂ) ^ (s + 1) / (s * (s + 1)))
      = (f n * (n : ℂ) / (n : ℂ)) * ((x : ℂ) ^ (s + 1) / (n : ℂ) ^ s / (s * (s + 1))) := by
        rw [mul_div_cancel_right₀ _ hn_c]
        ring
    _ = (f n * (n : ℂ)) * ((x : ℂ) ^ (s + 1) / ((n : ℂ) ^ s * (n : ℂ)) / (s * (s + 1))) := by
        ring

/-- For each `n : ℕ`, `0 < x`, and `0 < c`, the `n`-th term of the Dirichlet-Perron series is
integrable along `Re(s) = c`. -/
lemma integrable_term_mul_smoothedPerronKernel (f : ℕ → ℂ) {x c : ℝ} (hx : 0 < x)
    (hc : 0 < c) (n : ℕ) :
    Integrable (fun t : ℝ ↦
      LSeries.term f ((c : ℂ) + (t : ℂ) * I) n *
        smoothedPerronKernel x ((c : ℂ) + (t : ℂ) * I)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero]
  · have h_eq : (fun t : ℝ ↦
        LSeries.term f ((c : ℂ) + (t : ℂ) * I) n *
          smoothedPerronKernel x ((c : ℂ) + (t : ℂ) * I)) =
        fun t : ℝ ↦ (f n * (n : ℂ)) *
          smoothedPerronKernel (x / n) ((c : ℂ) + (t : ℂ) * I) := by
      ext t
      exact term_mul_smoothedPerronKernel_of_ne_zero hx hn _
    rw [h_eq]
    have hxn : 0 < x / n := div_pos hx (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
    exact (integrable_smoothedPerronKernel hxn hc).const_mul _

/-- Norm of `LSeries.term f (c + t * I) n` is independent of `t`. -/
lemma norm_term_ofReal_add_ofReal_mul_I (f : ℕ → ℂ) (c t : ℝ) (n : ℕ) :
    ‖LSeries.term f ((c : ℂ) + (t : ℂ) * I) n‖ = ‖LSeries.term f (c : ℂ) n‖ := by
  simp [LSeries.norm_term_eq]

/-- If `LSeriesSummable f c`, then the `L¹` norms of the Dirichlet-Perron terms along `Re(s) = c`
are summable over `n : ℕ`. -/
lemma summable_integral_norm_term_mul_smoothedPerronKernel {f : ℕ → ℂ} {x c : ℝ}
    (h_sum : LSeriesSummable f (c : ℂ)) :
    Summable (fun n : ℕ ↦ ∫ t : ℝ,
      ‖LSeries.term f ((c : ℂ) + (t : ℂ) * I) n *
        smoothedPerronKernel x ((c : ℂ) + (t : ℂ) * I)‖) := by
  have h_eq : (fun n : ℕ ↦ ∫ t : ℝ,
      ‖LSeries.term f ((c : ℂ) + (t : ℂ) * I) n *
        smoothedPerronKernel x ((c : ℂ) + (t : ℂ) * I)‖) =
      fun n : ℕ ↦ ‖LSeries.term f (c : ℂ) n‖ *
        ∫ t : ℝ, ‖smoothedPerronKernel x ((c : ℂ) + (t : ℂ) * I)‖ := by
    ext n
    simp_rw [norm_mul, norm_term_ofReal_add_ofReal_mul_I, integral_const_mul]
  rw [h_eq]
  exact h_sum.norm.mul_right _

/-- Evaluation of the `n`-th term integral in the smoothed Perron series. -/
lemma integral_term_mul_smoothedPerronKernel (f : ℕ → ℂ) {x c : ℝ} (hx : 0 < x)
    (hc : 0 < c) (n : ℕ) :
    (2 * (π : ℂ))⁻¹ * (∫ t : ℝ,
      LSeries.term f ((c : ℂ) + (t : ℂ) * I) n *
        smoothedPerronKernel x ((c : ℂ) + (t : ℂ) * I)) =
      if n = 0 then 0 else f n * ((max (x - n) 0 : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero]
  · simp only [hn, ↓reduceIte]
    have h_eq : (fun t : ℝ ↦
        LSeries.term f ((c : ℂ) + (t : ℂ) * I) n *
          smoothedPerronKernel x ((c : ℂ) + (t : ℂ) * I)) =
        fun t : ℝ ↦ (f n * (n : ℂ)) *
          smoothedPerronKernel (x / n) ((c : ℂ) + (t : ℂ) * I) := by
      ext t
      exact term_mul_smoothedPerronKernel_of_ne_zero hx hn _
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hxn : 0 < x / n := div_pos hx hn_pos
    rw [h_eq, integral_const_mul, ← mul_assoc, mul_comm (2 * (π : ℂ))⁻¹, mul_assoc,
      smoothed_perron_kernel_eval hxn hc, mul_assoc]
    congr 1
    have h_max : (n : ℝ) * max (x / n - 1) 0 = max (x - n) 0 := by
      rw [mul_max_of_nonneg _ _ hn_pos.le, mul_zero, mul_sub, mul_div_cancel₀ _ hn_pos.ne', mul_one]
    exact_mod_cast congr_arg ((↑) : ℝ → ℂ) h_max

/-- Reduction of the `tsum` of `if n = 0 then 0 else f n * max (x - n) 0` to `Finset.Icc 1 ⌊x⌋₊`. -/
lemma tsum_ite_mul_max_sub_eq_sum_Icc (f : ℕ → ℂ) {x : ℝ} (hx : 0 ≤ x) :
    (∑' n : ℕ, if n = 0 then (0 : ℂ) else f n * ((max (x - n) 0 : ℝ) : ℂ)) =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n * ((x : ℂ) - (n : ℂ)) := by
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊)]
  · refine Finset.sum_congr rfl fun n hn ↦ ?_
    rw [Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx).mp hn.2
    simp only [hn0, ↓reduceIte, max_eq_left (sub_nonneg.mpr hnx),
      Complex.ofReal_sub, Complex.ofReal_natCast]
  · intro n hn
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    rcases hn with hn0 | hnx
    · have h0 : n = 0 := by omega
      simp [h0]
    · rcases eq_or_ne n 0 with rfl | hn0
      · simp
      · have h_gt : x < (n : ℝ) := (Nat.floor_lt hx).mp hnx
        simp [hn0, max_eq_right (by linarith : x - (n : ℝ) ≤ 0)]

/-- **Smoothed Perron Formula for General L-Series**:
If `LSeriesSummable f c` with `0 < c` and `0 < x`, then
`∑ n ∈ Icc 1 ⌊x⌋₊, f n * (x - n) = (2 * π)⁻¹ * ∫ t : ℝ, LSeries f (c + t * I) * x^(c + 1 + t * I) /
((c + t * I)*(c + 1 + t * I))`. -/
theorem smoothed_perron_LSeries {f : ℕ → ℂ} {x c : ℝ} (hx : 0 < x) (hc : 0 < c)
    (h_sum : LSeriesSummable f (c : ℂ)) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n * ((x : ℂ) - (n : ℂ))) =
      (2 * (π : ℂ))⁻¹ * ∫ t : ℝ,
        LSeries f ((c : ℂ) + (t : ℂ) * I) *
          smoothedPerronKernel x ((c : ℂ) + (t : ℂ) * I) := by
  have h_pointwise (t : ℝ) :
      LSeries f ((c : ℂ) + (t : ℂ) * I) * smoothedPerronKernel x ((c : ℂ) + (t : ℂ) * I) =
        ∑' n : ℕ, LSeries.term f ((c : ℂ) + (t : ℂ) * I) n *
          smoothedPerronKernel x ((c : ℂ) + (t : ℂ) * I) := by
    rw [LSeries, tsum_mul_right]
  simp_rw [h_pointwise]
  rw [← integral_tsum_of_summable_integral_norm
    (integrable_term_mul_smoothedPerronKernel f hx hc)
    (summable_integral_norm_term_mul_smoothedPerronKernel h_sum)]
  rw [← tsum_mul_left]
  simp_rw [integral_term_mul_smoothedPerronKernel f hx hc]
  exact (tsum_ite_mul_max_sub_eq_sum_Icc f hx.le).symm

/-- **Smoothed Perron Formula for Chebyshev's `ψ₁(x) = ∑_{1 ≤ n ≤ x} Λ(n) * (x - n)`**:
For any `x > 0` and `c > 1`,
`∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) * (x - n) = (2 * π)⁻¹ * ∫ t : ℝ, (-deriv riemannZeta (c + t *
I) / riemannZeta (c + t * I)) * (x ^ (c + 1 + t * I) / ((c + t * I) * (c + 1 + t * I)))`. -/
theorem smoothed_perron_vonMangoldt {x c : ℝ} (hx : 0 < x) (hc : 1 < c) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) * ((x : ℂ) - (n : ℂ))) =
      (2 * (π : ℂ))⁻¹ * ∫ t : ℝ,
        (-deriv riemannZeta ((c : ℂ) + (t : ℂ) * I) / riemannZeta ((c : ℂ) + (t : ℂ) * I)) *
          ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I + 1) /
            (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))) := by
  have hc_re : 1 < (c : ℂ).re := by simpa using hc
  have h_sum : LSeriesSummable ↗Λ (c : ℂ) := ArithmeticFunction.LSeriesSummable_vonMangoldt hc_re
  rw [smoothed_perron_LSeries hx (zero_lt_one.trans hc) h_sum]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
  dsimp only
  have h_re_t : 1 < ((c : ℂ) + (t : ℂ) * I).re := by simpa using hc
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div h_re_t]
  rfl


/-!
## Section 1B: Connecting `psi1 x` to the Smoothed Perron Integral
-/

/-- The smoothed Perron integrand
$M(x, s) = \left(-\frac{\zeta'(s)}{\zeta(s)}\right) \frac{x^{s+1}}{s(s+1)}$. -/
noncomputable def smoothedPerronIntegrand (x : ℝ) (s : ℂ) : ℂ :=
  (-deriv riemannZeta s / riemannZeta s) * smoothedPerronKernel x s

theorem sum_Icc_vonMangoldt_eq_psi (t : ℝ) :
    ∑ k ∈ Icc 1 ⌊t⌋₊, (Λ k : ℝ) = Chebyshev.psi t := by
  rw [Chebyshev.psi, ← Icc_add_one_left_eq_Ioc, zero_add]

theorem sum_Icc_mul_vonMangoldt_eq_mul_psi_sub_psi1 {t : ℝ} (ht : 1 ≤ t) :
    ∑ k ∈ Icc 1 ⌊t⌋₊, (k : ℝ) * Λ k = t * Chebyshev.psi t - psi1 t := by
  have h := sum_mul_eq_sub_integral_mul₀ (c := fun k : ℕ ↦ (Λ k : ℝ)) (f := id)
    ArithmeticFunction.map_zero t (fun x _ ↦ differentiableAt_id) (by simp)
  have hsum0 : ∀ n : ℕ, ∑ k ∈ Icc 0 n, (k : ℝ) * Λ k = ∑ k ∈ Icc 1 n, (k : ℝ) * Λ k := by
    intro n
    rw [← insert_Icc_add_one_left_eq_Icc n.zero_le, sum_insert (by simp)]
    simp
  have hsum_psi : ∀ x : ℝ, ∑ k ∈ Icc 0 ⌊x⌋₊, (Λ k : ℝ) = Chebyshev.psi x := by
    intro x
    rw [← insert_Icc_add_one_left_eq_Icc (Nat.zero_le _), sum_insert (by simp),
      ArithmeticFunction.map_zero, zero_add, zero_add, sum_Icc_vonMangoldt_eq_psi]
  simp only [id_eq, deriv_id, one_mul, hsum0, hsum_psi] at h
  rw [h]
  unfold psi1
  rw [intervalIntegral.integral_of_le ht]

/-- For `1 ≤ x`, `psi1 x = ∑ n ∈ Icc 1 ⌊x⌋₊, (x - n) * Λ n`. -/
theorem psi1_eq_sum_Icc_sub_mul_vonMangoldt {x : ℝ} (hx : 1 ≤ x) :
    psi1 x = ∑ n ∈ Icc 1 ⌊x⌋₊, (x - n) * Λ n := by
  have h1 := sum_Icc_mul_vonMangoldt_eq_mul_psi_sub_psi1 hx
  have h2 := sum_Icc_vonMangoldt_eq_psi x
  have h3 : ∑ n ∈ Icc 1 ⌊x⌋₊, (x - n) * Λ n =
      x * (∑ n ∈ Icc 1 ⌊x⌋₊, (Λ n : ℝ)) - ∑ n ∈ Icc 1 ⌊x⌋₊, (n : ℝ) * Λ n := by
    simp only [sub_mul, sum_sub_distrib, ← mul_sum]
  rw [h2] at h3
  linarith

theorem ofReal_psi1_eq_sum_Icc_vonMangoldt {x : ℝ} (hx : 1 ≤ x) :
    (psi1 x : ℂ) = ∑ n ∈ Icc 1 ⌊x⌋₊, (Λ n : ℂ) * ((x : ℂ) - (n : ℂ)) := by
  rw [psi1_eq_sum_Icc_sub_mul_vonMangoldt hx]
  push_cast
  refine sum_congr rfl fun n _ ↦ ?_
  ring

/-- **Smoothed Perron Representation of `psi1 x`**:
For all `x ≥ 1` and `c > 1`,
$$(\psi_1(x) : \mathbb{C}) = \frac{1}{2\pi} \int_{-\infty}^\infty
  \text{smoothedPerronIntegrand}(x, c + t I)\,dt.$$ -/
theorem ofReal_psi1_eq_smoothedPerron_integral {x c : ℝ} (hx : 1 ≤ x) (hc : 1 < c) :
    (psi1 x : ℂ) =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ, smoothedPerronIntegrand x ((c : ℂ) + (t : ℂ) * I) := by
  have hx_pos : 0 < x := zero_lt_one.trans_le hx
  rw [ofReal_psi1_eq_sum_Icc_vonMangoldt hx, smoothed_perron_vonMangoldt hx_pos hc]
  rfl

/-- **Smoothed Perron Representation of `psi1 x` at `c = 2`**:
For all `x ≥ 1`,
$$(\psi_1(x) : \mathbb{C}) = \frac{1}{2\pi} \int_{-\infty}^\infty
  \text{smoothedPerronIntegrand}(x, 2 + t I)\,dt.$$ -/
theorem ofReal_psi1_eq_smoothedPerron_integral_two {x : ℝ} (hx : 1 ≤ x) :
    (psi1 x : ℂ) =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ, smoothedPerronIntegrand x (2 + (t : ℂ) * I) := by
  simpa using ofReal_psi1_eq_smoothedPerron_integral hx (by norm_num : (1 : ℝ) < 2)

/-!
## Section 2: Explicit Bound on `‖-deriv riemannZeta (2 + t * I) / riemannZeta (2 + t * I)‖ ≤ 2`
and Vertical Tail at $c = 2$
-/

/-- Telescoping majorant `(2 + log n) / n` for `log n / n^2`. -/
noncomputable def logTelescope (n : ℕ) : ℝ :=
  if n = 0 then 0 else (2 + Real.log n) / n

theorem logTelescope_one : logTelescope 1 = 2 := by
  simp [logTelescope]

theorem logTelescope_nonneg (n : ℕ) : 0 ≤ logTelescope n := by
  unfold logTelescope
  split_ifs with hn
  · exact le_rfl
  · have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
    positivity

/-- For every `n ≥ 2`, `Real.log n / n ^ 2 ≤ logTelescope (n - 1) - logTelescope n`. -/
theorem log_nat_div_sq_le_logTelescope_sub {n : ℕ} (hn : 2 ≤ n) :
    Real.log (n : ℝ) / (n : ℝ) ^ 2 ≤ logTelescope (n - 1) - logTelescope n := by
  have hn0 : n ≠ 0 := by omega
  have hn1 : n - 1 ≠ 0 := by omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hn1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by positivity
  have hn1_cast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hdiv_pos : 0 < (n : ℝ) / ((n - 1 : ℕ) : ℝ) := div_pos hn_pos hn1_pos
  have hlog_div : Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) ≤
      (n : ℝ) / ((n - 1 : ℕ) : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hdiv_pos
  rw [Real.log_div hn_pos.ne' hn1_pos.ne'] at hlog_div
  have hmul1 : ((n - 1 : ℕ) : ℝ) * (Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hlog_div hn1_pos.le
    have hrhs : ((n - 1 : ℕ) : ℝ) * ((n : ℝ) / ((n - 1 : ℕ) : ℝ) - 1) = 1 := by
      rw [hn1_cast]
      have : (n : ℝ) - 1 ≠ 0 := by rw [← hn1_cast]; exact hn1_pos.ne'
      field_simp
      ring
    linarith
  have hlog_mono : 0 ≤ Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ) := by
    refine sub_nonneg.mpr (Real.log_le_log hn1_pos ?_)
    exact_mod_cast Nat.sub_le n 1
  have hn_le_two : (n : ℝ) ≤ 2 * ((n - 1 : ℕ) : ℝ) := by
    rw [hn1_cast]
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hmul2 : (n : ℝ) * (Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ)) ≤ 2 := by
    calc
      (n : ℝ) * (Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ))
        ≤ (2 * ((n - 1 : ℕ) : ℝ)) * (Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hn_le_two hlog_mono
      _ = 2 * (((n - 1 : ℕ) : ℝ) * (Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ))) := by ring
      _ ≤ 2 * 1 := by linarith
      _ = 2 := by ring
  have hnum : Real.log (n : ℝ) ≤
      (n : ℝ) * (2 + Real.log ((n - 1 : ℕ) : ℝ)) - ((n - 1 : ℕ) : ℝ) * (2 + Real.log (n : ℝ)) := by
    rw [hn1_cast] at hmul2 ⊢
    linarith
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hden_le : (n : ℝ) * ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    rw [hn1_cast]
    nlinarith
  calc
    Real.log (n : ℝ) / (n : ℝ) ^ 2
      ≤ Real.log (n : ℝ) / ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_left hlog_nonneg (mul_pos hn_pos hn1_pos) hden_le
    _ ≤ ((n : ℝ) * (2 + Real.log ((n - 1 : ℕ) : ℝ)) -
          ((n - 1 : ℕ) : ℝ) * (2 + Real.log (n : ℝ))) / ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_right hnum (mul_pos hn_pos hn1_pos).le
    _ = logTelescope (n - 1) - logTelescope n := by
        simp only [logTelescope, hn0, hn1, ↓reduceIte]
        have h1 : (n : ℝ) ≠ 0 := hn_pos.ne'
        have h2 : ((n - 1 : ℕ) : ℝ) ≠ 0 := hn1_pos.ne'
        field_simp

theorem norm_term_vonMangoldt_two_add_mul_I_le (t : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    ‖LSeries.term (↗Λ) (2 + (t : ℂ) * I) n‖ ≤ logTelescope (n - 1) - logTelescope n := by
  rw [LSeries.norm_term_eq]
  have hn0 : n ≠ 0 := by omega
  simp only [hn0, ↓reduceIte, Complex.norm_real]
  rw [Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hre : ((2 : ℂ) + (t : ℂ) * I).re = 2 := by simp
  rw [hre, Real.rpow_two]
  refine (div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (sq_nonneg _)).trans ?_
  exact log_nat_div_sq_le_logTelescope_sub hn

theorem sum_range_norm_term_vonMangoldt_le_two_sub (t : ℝ) :
    ∀ N : ℕ, 2 ≤ N →
      ∑ n ∈ Finset.range N, ‖LSeries.term (↗Λ) (2 + (t : ℂ) * I) n‖ ≤
        2 - logTelescope (N - 1) := by
  intro N hN
  induction N with
  | zero => omega
  | succ m ihm =>
    rcases lt_or_ge m 2 with hm_lt | hm_ge
    · have hm1 : m = 1 := by omega
      subst hm1
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      simp [LSeries.term, logTelescope_one]
    · rw [Finset.sum_range_succ]
      have ih := ihm hm_ge
      have hterm := norm_term_vonMangoldt_two_add_mul_I_le t hm_ge
      have hsub : m + 1 - 1 = m := Nat.add_sub_cancel m 1
      rw [hsub]
      linarith

theorem sum_range_norm_term_vonMangoldt_le_two (t : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, ‖LSeries.term (↗Λ) (2 + (t : ℂ) * I) n‖ ≤ 2 := by
  rcases lt_or_ge N 2 with hlt | hge
  · interval_cases N
    · simp
    · simp [LSeries.term]
  · have h := sum_range_norm_term_vonMangoldt_le_two_sub t N hge
    linarith [logTelescope_nonneg (N - 1)]

theorem tsum_norm_term_vonMangoldt_le_two (t : ℝ) :
    ∑' n : ℕ, ‖LSeries.term (↗Λ) (2 + (t : ℂ) * I) n‖ ≤ 2 := by
  have hs : 1 < ((2 : ℂ) + (t : ℂ) * I).re := by simp
  have hsum : Summable (fun n : ℕ ↦ ‖LSeries.term (↗Λ) (2 + (t : ℂ) * I) n‖) :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).norm
  exact hsum.tsum_le_of_sum_range_le (sum_range_norm_term_vonMangoldt_le_two t)

/-- **Explicit Upper Bound on `-ζ'(2 + t I) / ζ(2 + t I)`**:
For all `t : ℝ`,
$$\left\|-\frac{\zeta'(2 + t I)}{\zeta(2 + t I)}\right\| \le 2.$$ -/
theorem norm_neg_deriv_riemannZeta_div_two_add_mul_I_le_two (t : ℝ) :
    ‖-deriv riemannZeta (2 + (t : ℂ) * I) / riemannZeta (2 + (t : ℂ) * I)‖ ≤ 2 := by
  have hs : 1 < ((2 : ℂ) + (t : ℂ) * I).re := by simp
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  unfold LSeries
  exact (norm_tsum_le_tsum_norm (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).norm).trans
    (tsum_norm_term_vonMangoldt_le_two t)

theorem norm_two_add_mul_I_sq (t : ℝ) :
    ‖(2 : ℂ) + (t : ℂ) * I‖ ^ 2 = t ^ 2 + 4 := by
  have h : (2 : ℂ) + (t : ℂ) * I = ⟨2, t⟩ := by
    apply Complex.ext <;> simp
  rw [h, Complex.sq_norm, Complex.normSq_mk]
  ring

theorem norm_three_add_mul_I_sq (t : ℝ) :
    ‖(2 : ℂ) + (t : ℂ) * I + 1‖ ^ 2 = t ^ 2 + 9 := by
  have h : (2 : ℂ) + (t : ℂ) * I + 1 = ⟨3, t⟩ := by
    apply Complex.ext
    · simp; norm_num
    · simp
  rw [h, Complex.sq_norm, Complex.normSq_mk]
  ring

theorem sq_add_four_le_norm_mul_two_add_mul_I (t : ℝ) :
    t ^ 2 + 4 ≤ ‖((2 : ℂ) + (t : ℂ) * I) * ((2 : ℂ) + (t : ℂ) * I + 1)‖ := by
  rw [norm_mul, ← norm_two_add_mul_I_sq t, sq]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [← abs_of_nonneg (norm_nonneg ((2 : ℂ) + (t : ℂ) * I)),
    ← abs_of_nonneg (norm_nonneg ((2 : ℂ) + (t : ℂ) * I + 1)), ← sq_le_sq,
    norm_two_add_mul_I_sq, norm_three_add_mul_I_sq]
  linarith

theorem norm_smoothedPerronKernel_two_add_mul_I_le {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖smoothedPerronKernel x (2 + (t : ℂ) * I)‖ ≤ x ^ (3 : ℝ) / (t ^ 2 + 4) := by
  unfold smoothedPerronKernel
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hre : ((2 : ℂ) + (t : ℂ) * I + 1).re = 3 := by simp; norm_num
  rw [hre]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le 3) (by positivity)
    (sq_add_four_le_norm_mul_two_add_mul_I t)

/-- **Pointwise Quadratic Decay Bound for `smoothedPerronIntegrand` at $c = 2$**:
For all `x > 0` and `t : ℝ`,
$$\|\text{smoothedPerronIntegrand}(x, 2 + t I)\| \le \frac{2 x^3}{t^2 + 4}.$$ -/
theorem norm_smoothedPerronIntegrand_two_add_mul_I_le {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖smoothedPerronIntegrand x (2 + (t : ℂ) * I)‖ ≤ 2 * x ^ (3 : ℝ) / (t ^ 2 + 4) := by
  unfold smoothedPerronIntegrand
  rw [norm_mul, mul_div_assoc]
  exact mul_le_mul (norm_neg_deriv_riemannZeta_div_two_add_mul_I_le_two t)
    (norm_smoothedPerronKernel_two_add_mul_I_le hx t)
    (norm_nonneg _) (by norm_num)

theorem integrable_smoothedPerronIntegrand_two {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ ↦ smoothedPerronIntegrand x (2 + (t : ℂ) * I)) := by
  have hcont : Continuous (fun t : ℝ ↦ smoothedPerronIntegrand x (2 + (t : ℂ) * I)) := by
    unfold smoothedPerronIntegrand smoothedPerronKernel
    refine Continuous.mul ?_ ?_
    · refine Continuous.div ?_ ?_ ?_
      · refine Continuous.neg ?_
        have hdiff : DifferentiableOn ℂ (deriv riemannZeta) {1}ᶜ :=
          (differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton).deriv.differentiableOn
        refine hdiff.continuousOn.comp_continuous (by fun_prop) fun t ↦ ?_
        intro h
        have hre := congrArg Complex.re h
        simp at hre
      · refine differentiableOn_riemannZeta.continuousOn.comp_continuous (by fun_prop) fun t ↦ ?_
        intro h
        have hre := congrArg Complex.re h
        simp at hre
      · intro t
        exact riemannZeta_ne_zero_of_one_lt_re (by simp)
    · refine Continuous.div ?_ (by fun_prop) ?_
      · have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
        refine Continuous.const_cpow (by fun_prop) (Or.inl hx0)
      · intro t
        have hpos : 0 < t ^ 2 + 4 := by positivity
        have hle := sq_add_four_le_norm_mul_two_add_mul_I t
        exact norm_ne_zero_iff.mp (hpos.trans_le hle).ne'
  have hdom : Integrable (fun t : ℝ ↦ (2 * x ^ (3 : ℝ)) * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul (2 * x ^ (3 : ℝ))
  refine hdom.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun t ↦ ?_)
  refine (norm_smoothedPerronIntegrand_two_add_mul_I_le hx t).trans ?_
  rw [div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact inv_anti₀ (by positivity) (by linarith)

theorem integral_Ioi_inv_sq_eq {U : ℝ} (hU : 0 < U) :
    ∫ t in Ioi U, (t ^ 2)⁻¹ = U⁻¹ := by
  have hcongr : EqOn (fun t : ℝ ↦ (t ^ 2)⁻¹) (fun t : ℝ ↦ t ^ (-2 : ℝ)) (Ioi U) := by
    intro t ht
    dsimp only
    have ht_pos : 0 < t := hU.trans ht
    rw [Real.rpow_neg ht_pos.le, ← Real.rpow_natCast t 2]
    norm_num
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_Ioi_rpow_of_lt (by norm_num) hU]
  have h1 : (-2 : ℝ) + 1 = -1 := by norm_num
  rw [h1, div_neg, div_one, neg_neg, Real.rpow_neg_one]

theorem integrableOn_Ioi_inv_sq {U : ℝ} (hU : 0 < U) :
    IntegrableOn (fun t : ℝ ↦ (t ^ 2)⁻¹) (Ioi U) := by
  refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hU).congr_fun ?_
    measurableSet_Ioi
  intro t ht
  dsimp only
  have ht_pos : 0 < t := hU.trans ht
  rw [Real.rpow_neg ht_pos.le, ← Real.rpow_natCast t 2]
  norm_num

theorem norm_setIntegral_Ioi_smoothedPerronIntegrand_two_le {x U : ℝ} (hx : 0 < x) (hU : 0 < U) :
    ‖∫ t in Ioi U, smoothedPerronIntegrand x (2 + (t : ℂ) * I)‖ ≤ 2 * x ^ (3 : ℝ) / U := by
  calc
    ‖∫ t in Ioi U, smoothedPerronIntegrand x (2 + (t : ℂ) * I)‖
      ≤ ∫ t in Ioi U, ‖smoothedPerronIntegrand x (2 + (t : ℂ) * I)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi U, (2 * x ^ (3 : ℝ)) * (t ^ 2)⁻¹ := by
        refine setIntegral_mono_on (integrable_smoothedPerronIntegrand_two hx).norm.integrableOn
          ((integrableOn_Ioi_inv_sq hU).const_mul (2 * x ^ (3 : ℝ))) measurableSet_Ioi fun t ht ↦ ?_
        have ht_pos : 0 < t := hU.trans ht
        refine (norm_smoothedPerronIntegrand_two_add_mul_I_le hx t).trans ?_
        rw [div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact inv_anti₀ (sq_pos_of_pos ht_pos) (by linarith)
    _ = 2 * x ^ (3 : ℝ) / U := by
        rw [integral_const_mul, integral_Ioi_inv_sq_eq hU, div_eq_mul_inv]

theorem norm_setIntegral_Iic_smoothedPerronIntegrand_two_le {x U : ℝ} (hx : 0 < x) (hU : 0 < U) :
    ‖∫ t in Iic (-U), smoothedPerronIntegrand x (2 + (t : ℂ) * I)‖ ≤ 2 * x ^ (3 : ℝ) / U := by
  have hsub : (∫ t in Iic (-U), smoothedPerronIntegrand x (2 + (t : ℂ) * I)) =
      ∫ t in Ioi U, smoothedPerronIntegrand x (2 + ((-t : ℝ) : ℂ) * I) := by
    rw [← integral_comp_neg_Ioi]
  rw [hsub]
  calc
    ‖∫ t in Ioi U, smoothedPerronIntegrand x (2 + ((-t : ℝ) : ℂ) * I)‖
      ≤ ∫ t in Ioi U, ‖smoothedPerronIntegrand x (2 + ((-t : ℝ) : ℂ) * I)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi U, (2 * x ^ (3 : ℝ)) * (t ^ 2)⁻¹ := by
        refine setIntegral_mono_on
          (((integrable_smoothedPerronIntegrand_two hx).comp_neg).norm.integrableOn)
          ((integrableOn_Ioi_inv_sq hU).const_mul (2 * x ^ (3 : ℝ))) measurableSet_Ioi fun t ht ↦ ?_
        have ht_pos : 0 < t := hU.trans ht
        have hb := norm_smoothedPerronIntegrand_two_add_mul_I_le hx (-t)
        rw [neg_sq] at hb
        refine hb.trans ?_
        rw [div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact inv_anti₀ (sq_pos_of_pos ht_pos) (by linarith)
    _ = 2 * x ^ (3 : ℝ) / U := by
        rw [integral_const_mul, integral_Ioi_inv_sq_eq hU, div_eq_mul_inv]

theorem norm_integral_sub_intervalIntegral_smoothedPerronIntegrand_two_le
    {x U : ℝ} (hx : 0 < x) (hU : 0 < U) :
    ‖(∫ t : ℝ, smoothedPerronIntegrand x (2 + (t : ℂ) * I)) -
      (∫ t in (-U)..U, smoothedPerronIntegrand x (2 + (t : ℂ) * I))‖ ≤
        4 * x ^ (3 : ℝ) / U := by
  have hint := integrable_smoothedPerronIntegrand_two hx
  have hle : -U ≤ U := by linarith
  rw [intervalIntegral.integral_of_le hle]
  have hcompl := integral_add_compl (s := Ioc (-U) U) measurableSet_Ioc hint
  have hsub : (∫ t : ℝ, smoothedPerronIntegrand x (2 + (t : ℂ) * I)) -
      (∫ t in Ioc (-U) U, smoothedPerronIntegrand x (2 + (t : ℂ) * I)) =
        ∫ t in (Ioc (-U) U)ᶜ, smoothedPerronIntegrand x (2 + (t : ℂ) * I) := by
    linear_combination -hcompl
  have hset : (Ioc (-U) U)ᶜ = Iic (-U) ∪ Ioi U := compl_Ioc
  have hdisj : Disjoint (Iic (-U)) (Ioi U) := by
    rw [Set.disjoint_iff]
    intro t ⟨ht1, ht2⟩
    rw [Set.mem_Iic] at ht1
    rw [Set.mem_Ioi] at ht2
    linarith
  rw [hsub, hset, setIntegral_union hdisj measurableSet_Ioi hint.integrableOn hint.integrableOn]
  calc
    ‖(∫ t in Iic (-U), smoothedPerronIntegrand x (2 + (t : ℂ) * I)) +
        (∫ t in Ioi U, smoothedPerronIntegrand x (2 + (t : ℂ) * I))‖
      ≤ ‖∫ t in Iic (-U), smoothedPerronIntegrand x (2 + (t : ℂ) * I)‖ +
          ‖∫ t in Ioi U, smoothedPerronIntegrand x (2 + (t : ℂ) * I)‖ := norm_add_le _ _
    _ ≤ 2 * x ^ (3 : ℝ) / U + 2 * x ^ (3 : ℝ) / U :=
        add_le_add (norm_setIntegral_Iic_smoothedPerronIntegrand_two_le hx hU)
          (norm_setIntegral_Ioi_smoothedPerronIntegrand_two_le hx hU)
    _ = 4 * x ^ (3 : ℝ) / U := by ring

/-- **Vertical Tail Bound at $c = 2$**:
For all `x > 0` and `U > 0`,
$$\left\|\frac{1}{2\pi} \int_{-\infty}^\infty \text{smoothedPerronIntegrand}(x, 2 + t I)\,dt
  - \frac{1}{2\pi} \int_{-U}^U \text{smoothedPerronIntegrand}(x, 2 + t I)\,dt\right\|
  \le \frac{2 x^3}{\pi U}.$$ -/
theorem norm_inv_two_pi_integral_sub_intervalIntegral_smoothedPerronIntegrand_two_le
    {x U : ℝ} (hx : 0 < x) (hU : 0 < U) :
    ‖(2 * (Real.pi : ℂ))⁻¹ * (∫ t : ℝ, smoothedPerronIntegrand x (2 + (t : ℂ) * I)) -
      (2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U, smoothedPerronIntegrand x (2 + (t : ℂ) * I))‖ ≤
        2 * x ^ (3 : ℝ) / (Real.pi * U) := by
  have h2pi : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    rw [← ofReal_ofNat, ← ofReal_mul, Complex.norm_real, Real.norm_of_nonneg Real.two_pi_pos.le]
  rw [← mul_sub, norm_mul, norm_inv, h2pi]
  calc
    (2 * Real.pi)⁻¹ *
        ‖(∫ t : ℝ, smoothedPerronIntegrand x (2 + (t : ℂ) * I)) -
          (∫ t in (-U)..U, smoothedPerronIntegrand x (2 + (t : ℂ) * I))‖
      ≤ (2 * Real.pi)⁻¹ * (4 * x ^ (3 : ℝ) / U) :=
        mul_le_mul_of_nonneg_left
          (norm_integral_sub_intervalIntegral_smoothedPerronIntegrand_two_le hx hU)
          (by positivity)
    _ = 2 * x ^ (3 : ℝ) / (Real.pi * U) := by
        have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
        have hU0 : U ≠ 0 := hU.ne'
        field_simp
        ring

/-- **Truncated Smoothed Perron Approximation to `psi1 x` at $c = 2$**:
For all `x ≥ 1` and `U > 0`,
$$\left\|(\psi_1(x) : \mathbb{C})
  - \frac{1}{2\pi} \int_{-U}^U \text{smoothedPerronIntegrand}(x, 2 + t I)\,dt\right\|
  \le \frac{2 x^3}{\pi U}.$$ -/
theorem norm_psi1_sub_truncated_smoothedPerron_two_le {x U : ℝ} (hx : 1 ≤ x) (hU : 0 < U) :
    ‖(psi1 x : ℂ) -
      (2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U, smoothedPerronIntegrand x (2 + (t : ℂ) * I))‖ ≤
        2 * x ^ (3 : ℝ) / (Real.pi * U) := by
  rw [ofReal_psi1_eq_smoothedPerron_integral_two hx]
  exact norm_inv_two_pi_integral_sub_intervalIntegral_smoothedPerronIntegrand_two_le
    (zero_lt_one.trans_le hx) hU

end ConjectureMachines.Semantics.Riemann.WeightedStieltjes
