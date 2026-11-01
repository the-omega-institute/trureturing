/- GID: D5/S3/Weil/Mertens/Cryptids/WeightedStieltjes
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/Cryptids/WeightedStieltjes
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

import D5.S3.Weil.Mertens.Cryptids.WeightedStieltjes.Smoothing

/-! Original WeightedStieltjes analytic supplier for the RH Chebyshev estimate. -/

namespace ConjectureMachines.Semantics.Riemann.WeightedStieltjes

open Complex Finset Filter MeasureTheory Set Asymptotics Topology
open scoped Real Topology Interval

/-- **Uniform Multiplicity-Weighted High-Frequency Quadratic Zero-Tail Bound**:
If `0 < T ≤ U`, `0 ≤ a`, `0 ≤ D`, and
`(weightedZeroCountingFunction t : ℝ) ≤ a * t * Real.log t + C * t + D` for all `t ∈ Set.Icc T U`,
then:
$$\sum_{\rho \in \mathcal{Z}(T, U)} \frac{m_\rho}{|\operatorname{Im} \rho|^2}
  \le \frac{2 a \log T + 2 a + 2 C}{T} + \frac{2 D}{T^2}$$
uniformly in `U` (completely independent of `U`!). -/
theorem sum_weighted_inv_sq_nontrivialZetaZerosBetween_le_of_riemannVonMangoldt
    {T U a C D : ℝ} (hT : 0 < T) (hTU : T ≤ U) (ha : 0 ≤ a) (hD : 0 ≤ D)
    (hN_bound : ∀ t ∈ Set.Icc T U,
      (weightedZeroCountingFunction t : ℝ) ≤ a * t * Real.log t + C * t + D) :
    (∑ ρ ∈ nontrivialZetaZerosBetween T U,
      (analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im| ^ 2) ≤
      (2 * a * Real.log T + 2 * a + 2 * C) / T + 2 * D / T ^ 2 := by
  have hU_pos : 0 < U := hT.trans_le hTU
  have hU_ne : U ≠ 0 := hU_pos.ne'
  rw [sum_weighted_inv_sq_nontrivialZetaZerosBetween_eq hT hTU]
  have hNT_nonneg : 0 ≤ (weightedZeroCountingFunction T : ℝ) / T ^ 2 := by positivity
  have hNU_le : (weightedZeroCountingFunction U : ℝ) / U ^ 2 ≤
      (a * Real.log U + C) / U + D / U ^ 2 := by
    have hU_in : U ∈ Set.Icc T U := ⟨hTU, le_rfl⟩
    have h1 : (weightedZeroCountingFunction U : ℝ) / U ^ 2 ≤
        (a * U * Real.log U + C * U + D) / U ^ 2 :=
      div_le_div_of_nonneg_right (hN_bound U hU_in) (sq_nonneg U)
    have h2 : (a * U * Real.log U + C * U + D) / U ^ 2 =
        (a * Real.log U + C) / U + D / U ^ 2 := by
      field_simp [hU_ne]
    rwa [h2] at h1
  have hU_term_nonneg : 0 ≤ (a * Real.log U + C) / U + D / U ^ 2 :=
    (by positivity : 0 ≤ (weightedZeroCountingFunction U : ℝ) / U ^ 2).trans hNU_le
  have haU_nonneg : 0 ≤ 2 * a / U := by positivity
  have hD_le : D / U ^ 2 ≤ D / T ^ 2 := by
    gcongr
  have hint_B :
      IntervalIntegrable (fun t : ℝ ↦ (a * t * Real.log t + C * t + D) / t ^ 3) volume T U := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hTU]
    refine (continuousOn_of_forall_continuousAt fun t ht ↦ ?_).integrableOn_Icc
    have ht_pos : 0 < t := hT.trans_le ht.1
    have ht_ne : t ≠ 0 := ht_pos.ne'
    refine ContinuousAt.div ?_ (continuousAt_id.pow 3) (pow_ne_zero 3 ht_ne)
    exact (((continuousAt_const.mul continuousAt_id).mul (Real.continuousAt_log ht_ne)).add
      (continuousAt_const.mul continuousAt_id)).add continuousAt_const
  have hint_le :
      (∫ t in T..U, (weightedZeroCountingFunction t : ℝ) / t ^ 3) ≤
        ((a * Real.log T + a + C) / T + D / (2 * T ^ 2)) -
          ((a * Real.log U + a + C) / U + D / (2 * U ^ 2)) := by
    rw [← intervalIntegral_riemannVonMangoldt_div_cube hT hTU a C D]
    refine intervalIntegral.integral_mono_on hTU
      (intervalIntegrable_weightedZeroCountingFunction_div_cube hT hTU) hint_B fun t ht ↦ ?_
    have ht_pos : 0 < t := hT.trans_le ht.1
    exact div_le_div_of_nonneg_right (hN_bound t ht) (by positivity)
  have h_id :
      ((a * Real.log U + C) / U + D / U ^ 2) +
          2 * (((a * Real.log T + a + C) / T + D / (2 * T ^ 2)) -
            ((a * Real.log U + a + C) / U + D / (2 * U ^ 2))) =
        (2 * a * Real.log T + 2 * a + 2 * C) / T + D / T ^ 2 + D / U ^ 2 -
          ((a * Real.log U + C) / U + D / U ^ 2) - 2 * a / U := by
    field_simp [hT.ne', hU_ne]
    ring
  have h_two_D : D / T ^ 2 + D / T ^ 2 = 2 * D / T ^ 2 := by ring
  linarith

/-- **Contour-Shift Explicit Bound with Multiplicity-Weighted Riemann–von Mangoldt Zero Sums**:
Combining `abs_psi_sub_self_le_smoothed_contour_shift` with the multiplicity-weighted low-frequency
and high-frequency Stieltjes bounds replaces both zero sums by `U`-independent expressions, leaving
`contourDiffError x h a U` as the **only** `U`-dependent term! -/
theorem abs_psi_sub_self_le_weighted_riemannVonMangoldt_add_contourDiffError
    (hRH : RiemannHypothesis) {x h t₀ T U a a_rvM C D : ℝ}
    (hx_sub : 1 ≤ x - h) (hh : 0 < h) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) (hTU : T ≤ U)
    (ha : -1 / 2 < a) (ha_neg : a < 0)
    (h0 : weightedZeroCountingFunction t₀ = 0)
    (ha_rvM : 0 ≤ a_rvM) (hD : 0 ≤ D)
    (hN_bound : ∀ t ∈ Set.Icc t₀ U,
      (weightedZeroCountingFunction t : ℝ) ≤ a_rvM * t * Real.log t + C * t + D)
    (h_no_horiz : ∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        Real.sqrt (x + h) *
          (a_rvM / 2 * (Real.log T) ^ 2 + (a_rvM + C) * Real.log T + C + D / t₀ -
            a_rvM / 2 * (Real.log t₀) ^ 2 - C * Real.log t₀) +
        (2 * (x + h) ^ (3 / 2 : ℝ) / h) *
          ((2 * a_rvM * Real.log T + 2 * a_rvM + 2 * C) / T + 2 * D / T ^ 2) +
        contourDiffError x h a U := by
  have hT : 0 < T := ht₀.trans_le ht₀T
  have h_base :=
    abs_psi_sub_self_le_smoothed_contour_shift hRH hx_sub hh hT hTU ha ha_neg h_no_horiz
  have h_low := sum_weighted_inv_norm_nontrivialZetaZerosUpTo_le_of_riemannVonMangoldt
    ht₀ ht₀T h0 (fun t ht ↦ hN_bound t ⟨ht.1, ht.2.trans hTU⟩)
  have h_high := sum_weighted_inv_sq_nontrivialZetaZerosBetween_le_of_riemannVonMangoldt
    hT hTU ha_rvM hD (fun t ht ↦ hN_bound t ⟨ht₀T.trans ht.1, ht.2⟩)
  have h_low_mul :
      Real.sqrt (x + h) *
          (∑ ρ ∈ nontrivialZetaZerosUpTo T,
            (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) ≤
        Real.sqrt (x + h) *
          (a_rvM / 2 * (Real.log T) ^ 2 + (a_rvM + C) * Real.log T + C + D / t₀ -
            a_rvM / 2 * (Real.log t₀) ^ 2 - C * Real.log t₀) :=
    mul_le_mul_of_nonneg_left h_low (Real.sqrt_nonneg _)
  have h_high_mul :
      (2 * (x + h) ^ (3 / 2 : ℝ) / h) *
          (∑ ρ ∈ nontrivialZetaZerosBetween T U,
            (analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im| ^ 2) ≤
        (2 * (x + h) ^ (3 / 2 : ℝ) / h) *
          ((2 * a_rvM * Real.log T + 2 * a_rvM + 2 * C) / T + 2 * D / T ^ 2) := by
    have hxh_pos : 0 ≤ x + h := by linarith
    exact mul_le_mul_of_nonneg_left h_high (by positivity)
  linarith

/-- The left-vertical component of `contourBoundaryError y a U` along `Re s = a`. -/
noncomputable def contourLeftVerticalError (y a U : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ‖∫ t in (-U)..U, smoothedPerronIntegrand y (a + (t : ℂ) * I)‖

/-- The horizontal component of `contourBoundaryError y a U` along `[a, 2] ± i U`. -/
noncomputable def contourHorizontalError (y a U : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ‖∫ σ in a..2, smoothedPerronIntegrand y (σ + (U : ℂ) * I)‖ +
    (2 * Real.pi)⁻¹ * ‖∫ σ in a..2, smoothedPerronIntegrand y (σ - (U : ℂ) * I)‖

theorem contourBoundaryError_eq_leftVertical_add_horizontal (y a U : ℝ) :
    contourBoundaryError y a U =
      contourLeftVerticalError y a U + contourHorizontalError y a U := by
  unfold contourBoundaryError contourLeftVerticalError contourHorizontalError
  ring

/-- The left-vertical difference-quotient error across `[x - h, x]` and `[x, x + h]`. -/
noncomputable def contourLeftVerticalDiffError (x h a U : ℝ) : ℝ :=
  max ((contourLeftVerticalError (x + h) a U + contourLeftVerticalError x a U) / h)
    ((contourLeftVerticalError x a U + contourLeftVerticalError (x - h) a U) / h)

/-- The `U`-dependent vertical-tail and horizontal-segment part of `contourDiffError x h a U`
that vanishes along zero-free heights `U → ∞`. -/
noncomputable def contourTailAndHorizontalDiffError (x h a U : ℝ) : ℝ :=
  4 * (x + h) ^ (3 : ℝ) / (Real.pi * h * U) +
    max ((contourHorizontalError (x + h) a U + contourHorizontalError x a U) / h)
      ((contourHorizontalError x a U + contourHorizontalError (x - h) a U) / h)

/-- Subadditivity of `contourDiffError` into its left-vertical and tail+horizontal parts. -/
theorem contourDiffError_le_leftVertical_add_tailAndHorizontal (x h a U : ℝ) :
    contourDiffError x h a U ≤
      contourLeftVerticalDiffError x h a U + contourTailAndHorizontalDiffError x h a U := by
  unfold contourDiffError contourLeftVerticalDiffError contourTailAndHorizontalDiffError
  simp only [contourBoundaryError_eq_leftVertical_add_horizontal]
  set L_fwd := (contourLeftVerticalError (x + h) a U + contourLeftVerticalError x a U) / h
  set L_bwd := (contourLeftVerticalError x a U + contourLeftVerticalError (x - h) a U) / h
  set H_fwd := (contourHorizontalError (x + h) a U + contourHorizontalError x a U) / h
  set H_bwd := (contourHorizontalError x a U + contourHorizontalError (x - h) a U) / h
  have h_fwd_eq :
      (contourLeftVerticalError (x + h) a U + contourHorizontalError (x + h) a U +
        (contourLeftVerticalError x a U + contourHorizontalError x a U)) / h =
      L_fwd + H_fwd := by
    dsimp [L_fwd, H_fwd]
    ring
  have h_bwd_eq :
      (contourLeftVerticalError x a U + contourHorizontalError x a U +
        (contourLeftVerticalError (x - h) a U + contourHorizontalError (x - h) a U)) / h =
      L_bwd + H_bwd := by
    dsimp [L_bwd, H_bwd]
    ring
  rw [h_fwd_eq, h_bwd_eq]
  have hmax : max (L_fwd + H_fwd) (L_bwd + H_bwd) ≤ max L_fwd L_bwd + max H_fwd H_bwd := by
    refine max_le ?_ ?_
    · exact add_le_add (le_max_left _ _) (le_max_left _ _)
    · exact add_le_add (le_max_right _ _) (le_max_right _ _)
  linarith

/-- **Eliminating `U` by Arbitrarily Large Zero-Free Heights (`U → ∞` Limit Theorem)**:
If for every `ε > 0` there exists a zero-free height `U ≥ T` (`∀ ρ ∈ nontrivialZetaZerosUpTo U,
|ρ.im| < U`)
such that `contourDiffError x h a U ≤ E_left + ε`, then `|Chebyshev.psi x - x|` is bounded by the
`U`-independent explicit formula bound with only `E_left` remaining! -/
theorem abs_psi_sub_self_le_weighted_riemannVonMangoldt_of_forall_pos
    (hRH : RiemannHypothesis) {x h t₀ T a a_rvM C D E_left : ℝ}
    (hx_sub : 1 ≤ x - h) (hh : 0 < h) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T)
    (ha : -1 / 2 < a) (ha_neg : a < 0)
    (h0 : weightedZeroCountingFunction t₀ = 0)
    (ha_rvM : 0 ≤ a_rvM) (hD : 0 ≤ D)
    (hN_bound : ∀ t ≥ t₀,
      (weightedZeroCountingFunction t : ℝ) ≤ a_rvM * t * Real.log t + C * t + D)
    (h_limit : ∀ ε > 0, ∃ U ≥ T,
      (∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) ∧
      contourDiffError x h a U ≤ E_left + ε) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        Real.sqrt (x + h) *
          (a_rvM / 2 * (Real.log T) ^ 2 + (a_rvM + C) * Real.log T + C + D / t₀ -
            a_rvM / 2 * (Real.log t₀) ^ 2 - C * Real.log t₀) +
        (2 * (x + h) ^ (3 / 2 : ℝ) / h) *
          ((2 * a_rvM * Real.log T + 2 * a_rvM + 2 * C) / T + 2 * D / T ^ 2) +
        E_left := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨U, hTU, h_no_horiz, h_err⟩ := h_limit ε hε
  have h_U := abs_psi_sub_self_le_weighted_riemannVonMangoldt_add_contourDiffError
    hRH hx_sub hh ht₀ ht₀T hTU ha ha_neg h0 ha_rvM hD
    (fun t ht ↦ hN_bound t ht.1) h_no_horiz
  linarith

/-- **Corollary Separating Uniform Left-Vertical Bound from Vanishing Tail + Horizontal Error**:
If `contourLeftVerticalDiffError x h a U ≤ E_left` for all `U ≥ T` and for every `ε > 0` there
exists a zero-free height `U ≥ T` with `contourTailAndHorizontalDiffError x h a U ≤ ε`, then
`|Chebyshev.psi x - x|` is bounded by the `U`-independent expression with `E_left`. -/
theorem abs_psi_sub_self_le_weighted_riemannVonMangoldt_add_left_vertical
    (hRH : RiemannHypothesis) {x h t₀ T a a_rvM C D E_left : ℝ}
    (hx_sub : 1 ≤ x - h) (hh : 0 < h) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T)
    (ha : -1 / 2 < a) (ha_neg : a < 0)
    (h0 : weightedZeroCountingFunction t₀ = 0)
    (ha_rvM : 0 ≤ a_rvM) (hD : 0 ≤ D)
    (hN_bound : ∀ t ≥ t₀,
      (weightedZeroCountingFunction t : ℝ) ≤ a_rvM * t * Real.log t + C * t + D)
    (h_left : ∀ U ≥ T, contourLeftVerticalDiffError x h a U ≤ E_left)
    (h_tail_horiz : ∀ ε > 0, ∃ U ≥ T,
      (∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) ∧
      contourTailAndHorizontalDiffError x h a U ≤ ε) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        Real.sqrt (x + h) *
          (a_rvM / 2 * (Real.log T) ^ 2 + (a_rvM + C) * Real.log T + C + D / t₀ -
            a_rvM / 2 * (Real.log t₀) ^ 2 - C * Real.log t₀) +
        (2 * (x + h) ^ (3 / 2 : ℝ) / h) *
          ((2 * a_rvM * Real.log T + 2 * a_rvM + 2 * C) / T + 2 * D / T ^ 2) +
        E_left := by
  refine abs_psi_sub_self_le_weighted_riemannVonMangoldt_of_forall_pos
    hRH hx_sub hh ht₀ ht₀T ha ha_neg h0 ha_rvM hD hN_bound fun ε hε ↦ ?_
  obtain ⟨U, hTU, h_no_horiz, h_th⟩ := h_tail_horiz ε hε
  refine ⟨U, hTU, h_no_horiz, ?_⟩
  have h_split := contourDiffError_le_leftVertical_add_tailAndHorizontal x h a U
  have h_l := h_left U hTU
  linarith

/-- On the line `Re s = -1 / 4`, `3 / 16 + t ^ 2 ≤ ‖((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I‖ * ‖((-1 / 4 :
ℝ) : ℂ) + (t : ℂ) * I + 1‖`. -/
theorem three_sixteenths_add_sq_le_norm_mul_neg_one_fourth (t : ℝ) :
    3 / 16 + t ^ 2 ≤
      ‖((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I‖ *
        ‖((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I + 1‖ := by
  set s : ℂ := ((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I
  have hs_sq : ‖s‖ ^ 2 = 1 / 16 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [s]
    ring
  have hs1_sq : ‖s + 1‖ ^ 2 = 9 / 16 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [s]
    ring
  rw [← sq_le_sq₀ (by positivity) (by positivity), mul_pow, hs_sq, hs1_sq]
  nlinarith [sq_nonneg t]

/-- For every `t : ℝ`,
`(|t| + 2) ^ 2 ≤ 32 * ‖(((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I) * (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I +
1)‖`. -/
theorem sq_abs_add_two_le_thirty_two_mul_norm_neg_one_fourth (t : ℝ) :
    (|t| + 2) ^ 2 ≤
      32 * ‖(((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I) *
        (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I + 1)‖ := by
  rw [norm_mul]
  have h1 := three_sixteenths_add_sq_le_norm_mul_neg_one_fourth t
  have h2 : (|t| + 2) ^ 2 ≤ 32 * (3 / 16 + t ^ 2) := by
    have h_abs_sq : |t| ^ 2 = t ^ 2 := sq_abs t
    nlinarith [abs_nonneg t, sq_nonneg (5 * |t| - 1)]
  linarith

/-- On `Re s = -1 / 4`, for `0 < y` and `t : ℝ`,
`‖smoothedPerronKernel y ((-1 / 4 : ℝ) + (t : ℂ) * I)‖ ≤ 32 * y ^ (3 / 4 : ℝ) / (|t| + 2) ^ 2`. -/
theorem norm_smoothedPerronKernel_neg_one_fourth_le {y : ℝ} (hy : 0 < y) (t : ℝ) :
    ‖smoothedPerronKernel y (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      32 * y ^ (3 / 4 : ℝ) / (|t| + 2) ^ 2 := by
  unfold smoothedPerronKernel
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  have hre : ((((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I) + 1).re = 3 / 4 := by
    simp
    norm_num
  rw [hre]
  have hden := sq_abs_add_two_le_thirty_two_mul_norm_neg_one_fourth t
  have hpos_sq : 0 < (|t| + 2) ^ 2 := by positivity
  have hden_div : (|t| + 2) ^ 2 / 32 ≤
      ‖(((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I) * (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I + 1)‖ := by
    linarith
  calc
    y ^ (3 / 4 : ℝ) /
        ‖(((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I) * (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I + 1)‖
      ≤ y ^ (3 / 4 : ℝ) / ((|t| + 2) ^ 2 / 32) :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le _) (by positivity) hden_div
    _ = 32 * y ^ (3 / 4 : ℝ) / (|t| + 2) ^ 2 := by
        rw [div_div_eq_mul_div]
        ring

/-- Pointwise bound on `‖smoothedPerronIntegrand y (-1 / 4 + t * I)‖` assuming a logarithmic bound
on `-ζ' / ζ` along `Re s = -1 / 4`. -/
theorem norm_smoothedPerronIntegrand_neg_one_fourth_le {y A B : ℝ} (hy : 0 < y) {t : ℝ}
    (h_zeta : ‖-deriv riemannZeta (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I) /
      riemannZeta (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ A * Real.log (|t| + 2) + B) :
    ‖smoothedPerronIntegrand y (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      32 * y ^ (3 / 4 : ℝ) * ((A * Real.log (|t| + 2) + B) / (|t| + 2) ^ 2) := by
  unfold smoothedPerronIntegrand
  rw [norm_mul]
  have h_AB_nonneg : 0 ≤ A * Real.log (|t| + 2) + B :=
    (norm_nonneg _).trans h_zeta
  calc
    ‖-deriv riemannZeta (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I) /
        riemannZeta (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I)‖ *
        ‖smoothedPerronKernel y (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ (A * Real.log (|t| + 2) + B) * (32 * y ^ (3 / 4 : ℝ) / (|t| + 2) ^ 2) :=
        mul_le_mul h_zeta (norm_smoothedPerronKernel_neg_one_fourth_le hy t)
          (norm_nonneg _) h_AB_nonneg
    _ = 32 * y ^ (3 / 4 : ℝ) * ((A * Real.log (|t| + 2) + B) / (|t| + 2) ^ 2) := by ring

/-- Exact derivative of `-(A * (1 + Real.log (t + 2)) + B) * (t + 2)⁻¹` for `t + 2 ≠ 0`. -/
theorem hasDerivAt_leftVerticalAntideriv (A B : ℝ) {t : ℝ} (ht : t + 2 ≠ 0) :
    HasDerivAt (fun x : ℝ ↦ -(A * (1 + Real.log (x + 2)) + B) * (x + 2)⁻¹)
      ((A * Real.log (t + 2) + B) / (t + 2) ^ 2) t := by
  have hd_add : HasDerivAt (fun x : ℝ ↦ x + 2) 1 t := (hasDerivAt_id t).add_const 2
  have hd_log : HasDerivAt (fun x : ℝ ↦ Real.log (x + 2)) (1 / (t + 2)) t :=
    hd_add.log ht
  have hd_inv : HasDerivAt (fun x : ℝ ↦ (x + 2)⁻¹) (-1 / (t + 2) ^ 2) t :=
    (hd_add.inv ht).congr_deriv (by ring)
  refine ((((hd_log.const_add 1).const_mul A).add_const B).neg.mul hd_inv).congr_deriv ?_
  simp only [Pi.neg_apply]
  field_simp [ht]
  ring

/-- **Exact Closed-Form Integral of `(A * Real.log (t + 2) + B) / (t + 2) ^ 2` on `[0, U]`**:
For `0 ≤ U`,
$$\int_0^U \frac{A \log(t + 2) + B}{(t + 2)^2} \, dt
  = \frac{A (1 + \log 2) + B}{2} - \frac{A (1 + \log(U + 2)) + B}{U + 2}.$$ -/
theorem intervalIntegral_log_add_two_div_sq_eq {U : ℝ} (hU : 0 ≤ U) (A B : ℝ) :
    (∫ t : ℝ in (0 : ℝ)..U, (A * Real.log (t + 2) + B) / (t + 2) ^ 2) =
      (A * (1 + Real.log 2) + B) / 2 -
        (A * (1 + Real.log (U + 2)) + B) / (U + 2) := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) U,
      HasDerivAt (fun x : ℝ ↦ -(A * (1 + Real.log (x + 2)) + B) * (x + 2)⁻¹)
        ((A * Real.log (t + 2) + B) / (t + 2) ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hU] at ht
    exact hasDerivAt_leftVerticalAntideriv A B (by linarith [ht.1])
  have hint : IntervalIntegrable
      (fun t : ℝ ↦ (A * Real.log (t + 2) + B) / (t + 2) ^ 2) volume 0 U := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hU]
    refine (continuousOn_of_forall_continuousAt fun t ht ↦ ?_).integrableOn_Icc
    have ht2 : t + 2 ≠ 0 := by linarith [ht.1]
    refine ContinuousAt.div ?_ ((continuousAt_id.add continuousAt_const).pow 2) (pow_ne_zero 2 ht2)
    exact ((continuousAt_const.mul ((continuousAt_id.add continuousAt_const).log ht2)).add
      continuousAt_const)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [zero_add]
  ring

/-- For `0 ≤ U`, `0 ≤ A`, and `0 ≤ B`,
`∫ t in 0..U, (A * Real.log (t + 2) + B) / (t + 2) ^ 2 ≤ (2 * A + B) / 2`. -/
theorem intervalIntegral_zero_to_U_log_add_two_div_sq_le
    {U A B : ℝ} (hU : 0 ≤ U) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (∫ t : ℝ in (0 : ℝ)..U, (A * Real.log (t + 2) + B) / (t + 2) ^ 2) ≤
      (2 * A + B) / 2 := by
  rw [intervalIntegral_log_add_two_div_sq_eq hU A B]
  have hlogU : 0 ≤ Real.log (U + 2) := Real.log_nonneg (by linarith)
  have h_upper_nonneg : 0 ≤ (A * (1 + Real.log (U + 2)) + B) / (U + 2) := by positivity
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h_lower_le : (A * (1 + Real.log 2) + B) / 2 ≤ (2 * A + B) / 2 := by
    nlinarith
  linarith

/-- Continuity of `t ↦ (A * Real.log (|t| + 2) + B) / (|t| + 2) ^ 2` on `ℝ`. -/
theorem continuous_log_abs_add_two_div_sq (A B : ℝ) :
    Continuous (fun t : ℝ ↦ (A * Real.log (|t| + 2) + B) / (|t| + 2) ^ 2) := by
  have h_add : Continuous (fun t : ℝ ↦ |t| + 2) := continuous_abs.add continuous_const
  have h_ne : ∀ t : ℝ, |t| + 2 ≠ 0 := fun t ↦ by positivity
  refine Continuous.div ?_ (h_add.pow 2) (fun t ↦ pow_ne_zero 2 (h_ne t))
  exact (continuous_const.mul (h_add.log h_ne)).add continuous_const

/-- For `0 ≤ U`, `0 ≤ A`, and `0 ≤ B`,
`∫ t in (-U)..U, (A * Real.log (|t| + 2) + B) / (|t| + 2) ^ 2 ≤ 2 * A + B`. -/
theorem intervalIntegral_neg_U_to_U_log_abs_add_two_div_sq_le
    {U A B : ℝ} (hU : 0 ≤ U) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (∫ t : ℝ in (-U)..U, (A * Real.log (|t| + 2) + B) / (|t| + 2) ^ 2) ≤
      2 * A + B := by
  let g : ℝ → ℝ := fun t ↦ (A * Real.log (|t| + 2) + B) / (|t| + 2) ^ 2
  have hg_cont : Continuous g := continuous_log_abs_add_two_div_sq A B
  have h_split : (∫ t in (-U)..U, g t) = (∫ t in (-U)..0, g t) + ∫ t in (0 : ℝ)..U, g t :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hg_cont.intervalIntegrable (-U) 0) (hg_cont.intervalIntegrable 0 U)).symm
  have h_neg : (∫ t in (-U)..0, g t) = ∫ t in (0 : ℝ)..U, g t := by
    have h1 := intervalIntegral.integral_comp_neg g (a := 0) (b := U)
    simp only [neg_zero, g, abs_neg] at h1
    exact h1.symm
  have h_pos_eq : (∫ t in (0 : ℝ)..U, g t) =
      ∫ t in (0 : ℝ)..U, (A * Real.log (t + 2) + B) / (t + 2) ^ 2 := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hU] at ht
    dsimp [g]
    rw [abs_of_nonneg ht.1]
  have h_pos_le := intervalIntegral_zero_to_U_log_add_two_div_sq_le hU hA hB
  linarith

/-- **Uniform Bound on `contourLeftVerticalError y (-1 / 4) U` (`U ≥ 0`)**:
If `‖-ζ'(-1 / 4 + t * I) / ζ(-1 / 4 + t * I)‖ ≤ A * Real.log (|t| + 2) + B` (`0 ≤ A, 0 ≤ B`),
then for all `y > 0` and `U ≥ 0`:
$$\text{contourLeftVerticalError}(y, -1/4, U)
  \le (2\pi)^{-1} \left(32 y^{3/4} (2 A + B)\right).$$ -/
theorem contourLeftVerticalError_neg_one_fourth_le
    {y U A B : ℝ} (hy : 0 < y) (hU : 0 ≤ U) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h_zeta : ∀ t : ℝ,
      ‖-deriv riemannZeta (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I) /
        riemannZeta (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ A * Real.log (|t| + 2) + B) :
    contourLeftVerticalError y (-1 / 4) U ≤
      (2 * Real.pi)⁻¹ * (32 * y ^ (3 / 4 : ℝ) * (2 * A + B)) := by
  unfold contourLeftVerticalError
  gcongr
  let g : ℝ → ℝ := fun t ↦ (A * Real.log (|t| + 2) + B) / (|t| + 2) ^ 2
  have hg_cont : Continuous (fun t : ℝ ↦ 32 * y ^ (3 / 4 : ℝ) * g t) :=
    continuous_const.mul (continuous_log_abs_add_two_div_sq A B)
  have h_norm_le :
      ‖∫ t in (-U)..U, smoothedPerronIntegrand y (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        ∫ t in (-U)..U, 32 * y ^ (3 / 4 : ℝ) * g t := by
    rw [intervalIntegral.integral_of_le (by linarith : -U ≤ U),
      intervalIntegral.integral_of_le (by linarith : -U ≤ U)]
    exact norm_integral_le_of_norm_le
      (hg_cont.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (ae_of_all _ fun t ↦ norm_smoothedPerronIntegrand_neg_one_fourth_le hy (h_zeta t))
  rw [intervalIntegral.integral_const_mul] at h_norm_le
  refine h_norm_le.trans ?_
  exact mul_le_mul_of_nonneg_left
    (intervalIntegral_neg_U_to_U_log_abs_add_two_div_sq_le hU hA hB) (by positivity)

/-- **Uniform Bound on `contourLeftVerticalDiffError x h (-1 / 4) U` (`U ≥ 0`)**:
For `1 ≤ x - h`, `0 < h`, and `0 ≤ U`,
$$\text{contourLeftVerticalDiffError}(x, h, -1/4, U)
  \le \frac{32 (2 A + B)}{\pi h} (x + h)^{3/4}.$$ -/
theorem contourLeftVerticalDiffError_neg_one_fourth_le
    {x h U A B : ℝ} (hx_sub : 1 ≤ x - h) (hh : 0 < h) (hU : 0 ≤ U) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h_zeta : ∀ t : ℝ,
      ‖-deriv riemannZeta (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I) /
        riemannZeta (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ A * Real.log (|t| + 2) + B) :
    contourLeftVerticalDiffError x h (-1 / 4) U ≤
      32 * (2 * A + B) / (Real.pi * h) * (x + h) ^ (3 / 4 : ℝ) := by
  have hx_minus_pos : 0 < x - h := zero_lt_one.trans_le hx_sub
  have hx_pos : 0 < x := by linarith
  have hx_plus_pos : 0 < x + h := by linarith
  have h_plus := contourLeftVerticalError_neg_one_fourth_le hx_plus_pos hU hA hB h_zeta
  have h_x := contourLeftVerticalError_neg_one_fourth_le hx_pos hU hA hB h_zeta
  have h_minus := contourLeftVerticalError_neg_one_fourth_le hx_minus_pos hU hA hB h_zeta
  have hrpow_x : x ^ (3 / 4 : ℝ) ≤ (x + h) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow hx_pos.le (by linarith) (by norm_num)
  have hrpow_minus : (x - h) ^ (3 / 4 : ℝ) ≤ (x + h) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow hx_minus_pos.le (by linarith) (by norm_num)
  have h_x_le : (2 * Real.pi)⁻¹ * (32 * x ^ (3 / 4 : ℝ) * (2 * A + B)) ≤
      (2 * Real.pi)⁻¹ * (32 * (x + h) ^ (3 / 4 : ℝ) * (2 * A + B)) := by
    gcongr
  have h_minus_le : (2 * Real.pi)⁻¹ * (32 * (x - h) ^ (3 / 4 : ℝ) * (2 * A + B)) ≤
      (2 * Real.pi)⁻¹ * (32 * (x + h) ^ (3 / 4 : ℝ) * (2 * A + B)) := by
    gcongr
  have h_alg :
      ((2 * Real.pi)⁻¹ * (32 * (x + h) ^ (3 / 4 : ℝ) * (2 * A + B)) +
        (2 * Real.pi)⁻¹ * (32 * (x + h) ^ (3 / 4 : ℝ) * (2 * A + B))) / h =
      32 * (2 * A + B) / (Real.pi * h) * (x + h) ^ (3 / 4 : ℝ) := by
    field_simp [Real.pi_ne_zero, hh.ne']
    ring
  unfold contourLeftVerticalDiffError
  refine max_le ?_ ?_
  · rw [← h_alg]
    exact div_le_div_of_nonneg_right (by linarith) hh.le
  · rw [← h_alg]
    exact div_le_div_of_nonneg_right (by linarith) hh.le

/-- On any horizontal segment `s = σ + t * I` (`t ≠ 0`, `σ ≤ 2`) with `1 ≤ y`,
`‖smoothedPerronKernel y ((σ : ℂ) + (t : ℂ) * I)‖ ≤ y ^ (3 : ℝ) / t ^ 2`. -/
theorem norm_smoothedPerronKernel_horizontal_le
    {y σ t : ℝ} (hy : 1 ≤ y) (hσ : σ ≤ 2) (ht : t ≠ 0) :
    ‖smoothedPerronKernel y ((σ : ℂ) + (t : ℂ) * I)‖ ≤ y ^ (3 : ℝ) / t ^ 2 := by
  have hy_pos : 0 < y := zero_lt_one.trans_le hy
  unfold smoothedPerronKernel
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy_pos]
  have hre : (((σ : ℂ) + (t : ℂ) * I) + 1).re = σ + 1 := by simp
  rw [hre]
  have hrpow : y ^ (σ + 1) ≤ y ^ (3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hy (by linarith)
  have hden : t ^ 2 ≤ ‖((σ : ℂ) + (t : ℂ) * I) * (((σ : ℂ) + (t : ℂ) * I) + 1)‖ := by
    have h1 := sq_abs_im_le_norm_mul_add_one ((σ : ℂ) + (t : ℂ) * I)
    simpa [sq_abs] using h1
  have ht_sq_pos : 0 < t ^ 2 := sq_pos_of_ne_zero ht
  calc
    y ^ (σ + 1) / ‖((σ : ℂ) + (t : ℂ) * I) * (((σ : ℂ) + (t : ℂ) * I) + 1)‖
      ≤ y ^ (3 : ℝ) / ‖((σ : ℂ) + (t : ℂ) * I) * (((σ : ℂ) + (t : ℂ) * I) + 1)‖ :=
        div_le_div_of_nonneg_right hrpow (norm_nonneg _)
    _ ≤ y ^ (3 : ℝ) / t ^ 2 :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hy_pos.le _) ht_sq_pos hden

/-- Bound on the top horizontal integral `∫ σ in (-1 / 4)..2, smoothedPerronIntegrand y (σ + U *
I)`. -/
theorem norm_integral_smoothedPerronIntegrand_top_neg_one_fourth_le
    {y U M_horiz : ℝ} (hy : 1 ≤ y) (hU : 0 < U)
    (h_top : ∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
      ‖-deriv riemannZeta ((σ : ℂ) + (U : ℂ) * I) /
        riemannZeta ((σ : ℂ) + (U : ℂ) * I)‖ ≤ M_horiz) :
    ‖∫ σ in (-1 / 4 : ℝ)..2, smoothedPerronIntegrand y ((σ : ℂ) + (U : ℂ) * I)‖ ≤
      9 / 4 * y ^ (3 : ℝ) * M_horiz / U ^ 2 := by
  have hy_pos : 0 < y := zero_lt_one.trans_le hy
  have hM_nonneg : 0 ≤ M_horiz :=
    (norm_nonneg _).trans (h_top 2 ⟨by norm_num, le_rfl⟩)
  have h_int :
      ‖∫ σ in (-1 / 4 : ℝ)..2, smoothedPerronIntegrand y ((σ : ℂ) + (U : ℂ) * I)‖ ≤
        (M_horiz * (y ^ (3 : ℝ) / U ^ 2)) * |2 - (-1 / 4 : ℝ)| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ ↦ ?_
    have hσ_icc : σ ∈ Set.Icc (-1 / 4 : ℝ) 2 := by
      rw [← Set.uIcc_of_le (by norm_num : (-1 / 4 : ℝ) ≤ 2)]
      exact uIoc_subset_uIcc hσ
    unfold smoothedPerronIntegrand
    rw [norm_mul]
    exact mul_le_mul (h_top σ hσ_icc)
      (norm_smoothedPerronKernel_horizontal_le hy hσ_icc.2 hU.ne')
      (norm_nonneg _) hM_nonneg
  have habs : |2 - (-1 / 4 : ℝ)| = 9 / 4 := by norm_num
  rw [habs] at h_int
  refine h_int.trans_eq ?_
  ring

/-- Bound on the bottom horizontal integral `∫ σ in (-1 / 4)..2, smoothedPerronIntegrand y (σ - U *
I)`. -/
theorem norm_integral_smoothedPerronIntegrand_bottom_neg_one_fourth_le
    {y U M_horiz : ℝ} (hy : 1 ≤ y) (hU : 0 < U)
    (h_bot : ∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
      ‖-deriv riemannZeta ((σ : ℂ) - (U : ℂ) * I) /
        riemannZeta ((σ : ℂ) - (U : ℂ) * I)‖ ≤ M_horiz) :
    ‖∫ σ in (-1 / 4 : ℝ)..2, smoothedPerronIntegrand y ((σ : ℂ) - (U : ℂ) * I)‖ ≤
      9 / 4 * y ^ (3 : ℝ) * M_horiz / U ^ 2 := by
  have hy_pos : 0 < y := zero_lt_one.trans_le hy
  have hM_nonneg : 0 ≤ M_horiz :=
    (norm_nonneg _).trans (h_bot 2 ⟨by norm_num, le_rfl⟩)
  have h_int :
      ‖∫ σ in (-1 / 4 : ℝ)..2, smoothedPerronIntegrand y ((σ : ℂ) - (U : ℂ) * I)‖ ≤
        (M_horiz * (y ^ (3 : ℝ) / U ^ 2)) * |2 - (-1 / 4 : ℝ)| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ ↦ ?_
    have hσ_icc : σ ∈ Set.Icc (-1 / 4 : ℝ) 2 := by
      rw [← Set.uIcc_of_le (by norm_num : (-1 / 4 : ℝ) ≤ 2)]
      exact uIoc_subset_uIcc hσ
    have h_sub_eq : (σ : ℂ) - (U : ℂ) * I = (σ : ℂ) + ((-U : ℝ) : ℂ) * I := by
      push_cast
      ring
    unfold smoothedPerronIntegrand
    rw [norm_mul]
    refine mul_le_mul (h_bot σ hσ_icc) ?_ (norm_nonneg _) hM_nonneg
    rw [h_sub_eq]
    have h_k := norm_smoothedPerronKernel_horizontal_le (t := -U) hy hσ_icc.2
      (neg_ne_zero.mpr hU.ne')
    simpa using h_k
  have habs : |2 - (-1 / 4 : ℝ)| = 9 / 4 := by norm_num
  rw [habs] at h_int
  refine h_int.trans_eq ?_
  ring

/-- Combined bound on `contourHorizontalError y (-1 / 4) U`. -/
theorem contourHorizontalError_neg_one_fourth_le
    {y U M_horiz : ℝ} (hy : 1 ≤ y) (hU : 0 < U)
    (h_top : ∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
      ‖-deriv riemannZeta ((σ : ℂ) + (U : ℂ) * I) /
        riemannZeta ((σ : ℂ) + (U : ℂ) * I)‖ ≤ M_horiz)
    (h_bot : ∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
      ‖-deriv riemannZeta ((σ : ℂ) - (U : ℂ) * I) /
        riemannZeta ((σ : ℂ) - (U : ℂ) * I)‖ ≤ M_horiz) :
    contourHorizontalError y (-1 / 4) U ≤
      9 / (4 * Real.pi) * y ^ (3 : ℝ) * M_horiz / U ^ 2 := by
  unfold contourHorizontalError
  have h1 := norm_integral_smoothedPerronIntegrand_top_neg_one_fourth_le hy hU h_top
  have h2 := norm_integral_smoothedPerronIntegrand_bottom_neg_one_fourth_le hy hU h_bot
  have h_alg :
      (2 * Real.pi)⁻¹ * (9 / 4 * y ^ (3 : ℝ) * M_horiz / U ^ 2) +
        (2 * Real.pi)⁻¹ * (9 / 4 * y ^ (3 : ℝ) * M_horiz / U ^ 2) =
      9 / (4 * Real.pi) * y ^ (3 : ℝ) * M_horiz / U ^ 2 := by
    field_simp [Real.pi_ne_zero, hU.ne']
    ring
  rw [← h_alg]
  gcongr

/-- **Explicit Bound on `contourTailAndHorizontalDiffError x h (-1 / 4) U`**:
For `1 ≤ x - h`, `0 < h`, and `0 < U`, if `‖-ζ' / ζ‖ ≤ M_horiz` along `[-1 / 4, 2] ± i U`, then:
$$\text{contourTailAndHorizontalDiffError}(x, h, -1/4, U)
  \le \frac{4 (x + h)^3}{\pi h U} + \frac{9 (x + h)^3 M_{\text{horiz}}}{2 \pi h U^2}.$$ -/
theorem contourTailAndHorizontalDiffError_neg_one_fourth_le
    {x h U M_horiz : ℝ} (hx_sub : 1 ≤ x - h) (hh : 0 < h) (hU : 0 < U)
    (h_top : ∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
      ‖-deriv riemannZeta ((σ : ℂ) + (U : ℂ) * I) /
        riemannZeta ((σ : ℂ) + (U : ℂ) * I)‖ ≤ M_horiz)
    (h_bot : ∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
      ‖-deriv riemannZeta ((σ : ℂ) - (U : ℂ) * I) /
        riemannZeta ((σ : ℂ) - (U : ℂ) * I)‖ ≤ M_horiz) :
    contourTailAndHorizontalDiffError x h (-1 / 4) U ≤
      4 * (x + h) ^ (3 : ℝ) / (Real.pi * h * U) +
        9 * (x + h) ^ (3 : ℝ) * M_horiz / (2 * Real.pi * h * U ^ 2) := by
  have hx : 1 ≤ x := by linarith
  have hx_plus : 1 ≤ x + h := by linarith
  have hM_nonneg : 0 ≤ M_horiz :=
    (norm_nonneg _).trans (h_top 2 ⟨by norm_num, le_rfl⟩)
  have h_plus := contourHorizontalError_neg_one_fourth_le hx_plus hU h_top h_bot
  have h_x := contourHorizontalError_neg_one_fourth_le hx hU h_top h_bot
  have h_minus := contourHorizontalError_neg_one_fourth_le hx_sub hU h_top h_bot
  have hrpow_x : x ^ (3 : ℝ) ≤ (x + h) ^ (3 : ℝ) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  have hrpow_minus : (x - h) ^ (3 : ℝ) ≤ (x + h) ^ (3 : ℝ) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  have h_x_le : 9 / (4 * Real.pi) * x ^ (3 : ℝ) * M_horiz / U ^ 2 ≤
      9 / (4 * Real.pi) * (x + h) ^ (3 : ℝ) * M_horiz / U ^ 2 := by
    gcongr
  have h_minus_le : 9 / (4 * Real.pi) * (x - h) ^ (3 : ℝ) * M_horiz / U ^ 2 ≤
      9 / (4 * Real.pi) * (x + h) ^ (3 : ℝ) * M_horiz / U ^ 2 := by
    gcongr
  have h_alg :
      (9 / (4 * Real.pi) * (x + h) ^ (3 : ℝ) * M_horiz / U ^ 2 +
        9 / (4 * Real.pi) * (x + h) ^ (3 : ℝ) * M_horiz / U ^ 2) / h =
      9 * (x + h) ^ (3 : ℝ) * M_horiz / (2 * Real.pi * h * U ^ 2) := by
    field_simp [Real.pi_ne_zero, hh.ne', hU.ne']
    ring
  unfold contourTailAndHorizontalDiffError
  gcongr
  refine max_le ?_ ?_
  · rw [← h_alg]
    exact div_le_div_of_nonneg_right (by linarith) hh.le
  · rw [← h_alg]
    exact div_le_div_of_nonneg_right (by linarith) hh.le

/-- Elementary quantitative decay bound: for all `1 ≤ U`, `(Real.log U) ^ 5 ≤ 3125 * U`. -/
theorem log_pow_five_le_mul_self {U : ℝ} (hU : 1 ≤ U) :
    (Real.log U) ^ 5 ≤ 3125 * U := by
  have hU_pos : 0 < U := zero_lt_one.trans_le hU
  have hrpow_pos : 0 < U ^ (1 / 5 : ℝ) := Real.rpow_pos_of_pos hU_pos (1 / 5)
  have hlog_rpow : Real.log (U ^ (1 / 5 : ℝ)) = 1 / 5 * Real.log U :=
    Real.log_rpow hU_pos (1 / 5)
  have hlog_le : Real.log (U ^ (1 / 5 : ℝ)) ≤ U ^ (1 / 5 : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hrpow_pos
  have hlog_bound : Real.log U ≤ 5 * U ^ (1 / 5 : ℝ) := by linarith
  calc
    (Real.log U) ^ 5 ≤ (5 * U ^ (1 / 5 : ℝ)) ^ 5 :=
      pow_le_pow_left₀ (Real.log_nonneg hU) hlog_bound 5
    _ = 3125 * (U ^ (1 / 5 : ℝ)) ^ (5 : ℕ) := by ring
    _ = 3125 * U := by
      rw [← Real.rpow_natCast (U ^ (1 / 5 : ℝ)) 5, ← Real.rpow_mul hU_pos.le]
      norm_num

/-- When `M_horiz ≤ C_h * (Real.log U) ^ 5` (`0 ≤ C_h`, `1 ≤ U`),
`contourTailAndHorizontalDiffError x h (-1 / 4) U` is bounded by `O(1 / U)`:
$$\text{contourTailAndHorizontalDiffError}(x, h, -1/4, U)
  \le \frac{(x + h)^3 (4 + \frac{28125}{2} C_h)}{\pi h U}.$$ -/
theorem contourTailAndHorizontalDiffError_neg_one_fourth_le_inv_U
    {x h U M_horiz C_h : ℝ} (hx_sub : 1 ≤ x - h) (hh : 0 < h) (hU : 1 ≤ U) (hCh : 0 ≤ C_h)
    (hM : M_horiz ≤ C_h * (Real.log U) ^ 5)
    (h_top : ∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
      ‖-deriv riemannZeta ((σ : ℂ) + (U : ℂ) * I) /
        riemannZeta ((σ : ℂ) + (U : ℂ) * I)‖ ≤ M_horiz)
    (h_bot : ∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
      ‖-deriv riemannZeta ((σ : ℂ) - (U : ℂ) * I) /
        riemannZeta ((σ : ℂ) - (U : ℂ) * I)‖ ≤ M_horiz) :
    contourTailAndHorizontalDiffError x h (-1 / 4) U ≤
      (x + h) ^ (3 : ℝ) * (4 + 28125 / 2 * C_h) / (Real.pi * h * U) := by
  have hU_pos : 0 < U := zero_lt_one.trans_le hU
  have hx_plus_pos : 0 < x + h := by linarith
  have h1 := contourTailAndHorizontalDiffError_neg_one_fourth_le hx_sub hh hU_pos h_top h_bot
  have h2 : 9 * (x + h) ^ (3 : ℝ) * M_horiz / (2 * Real.pi * h * U ^ 2) ≤
      9 * (x + h) ^ (3 : ℝ) * (C_h * (3125 * U)) / (2 * Real.pi * h * U ^ 2) := by
    have hM_le : M_horiz ≤ C_h * (3125 * U) :=
      hM.trans (mul_le_mul_of_nonneg_left (log_pow_five_le_mul_self hU) hCh)
    gcongr
  have h3 :
      4 * (x + h) ^ (3 : ℝ) / (Real.pi * h * U) +
        9 * (x + h) ^ (3 : ℝ) * (C_h * (3125 * U)) / (2 * Real.pi * h * U ^ 2) =
      (x + h) ^ (3 : ℝ) * (4 + 28125 / 2 * C_h) / (Real.pi * h * U) := by
    field_simp [Real.pi_ne_zero, hh.ne', hU_pos.ne']
    ring
  linarith

/-- **Existence of Arbitrarily Large Zero-Free Heights with `contourTailAndHorizontalDiffError ≤
ε`**:
If for every `U₀ ≥ T` there exists a zero-free height `U ≥ U₀` (`∀ ρ ∈ nontrivialZetaZerosUpTo U,
|ρ.im| < U`)
where `‖-ζ' / ζ‖ ≤ C_h * (Real.log U) ^ 5` along `[-1 / 4, 2] ± i U`, then for every `ε > 0`
there exists `U ≥ T` with `contourTailAndHorizontalDiffError x h (-1 / 4) U ≤ ε`. -/
theorem exists_zero_free_height_with_small_tailAndHorizontal
    {x h T C_h : ℝ} (hx_sub : 1 ≤ x - h) (hh : 0 < h) (hCh : 0 ≤ C_h)
    (h_heights : ∀ U₀ ≥ T, ∃ U ≥ U₀,
      (∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) ∧
      (∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
        ‖-deriv riemannZeta ((σ : ℂ) + (U : ℂ) * I) /
          riemannZeta ((σ : ℂ) + (U : ℂ) * I)‖ ≤ C_h * (Real.log U) ^ 5) ∧
      (∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
        ‖-deriv riemannZeta ((σ : ℂ) - (U : ℂ) * I) /
          riemannZeta ((σ : ℂ) - (U : ℂ) * I)‖ ≤ C_h * (Real.log U) ^ 5)) :
    ∀ ε > 0, ∃ U ≥ T,
      (∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) ∧
      contourTailAndHorizontalDiffError x h (-1 / 4) U ≤ ε := by
  intro ε hε
  set K : ℝ := (x + h) ^ (3 : ℝ) * (4 + 28125 / 2 * C_h) / (Real.pi * h)
  set U₀ : ℝ := max T (max 1 (K / ε))
  have hT_le_U₀ : T ≤ U₀ := le_max_left _ _
  have h1_le_U₀ : 1 ≤ U₀ := (le_max_left 1 (K / ε)).trans (le_max_right T _)
  have hKε_le_U₀ : K / ε ≤ U₀ := (le_max_right 1 (K / ε)).trans (le_max_right T _)
  obtain ⟨U, hU₀_le, h_no_horiz, h_top, h_bot⟩ := h_heights U₀ hT_le_U₀
  have hTU : T ≤ U := hT_le_U₀.trans hU₀_le
  have h1U : 1 ≤ U := h1_le_U₀.trans hU₀_le
  have hU_pos : 0 < U := zero_lt_one.trans_le h1U
  have hKε_le_U : K / ε ≤ U := hKε_le_U₀.trans hU₀_le
  refine ⟨U, hTU, h_no_horiz, ?_⟩
  have h_bound := contourTailAndHorizontalDiffError_neg_one_fourth_le_inv_U
    hx_sub hh h1U hCh le_rfl h_top h_bot
  have h_eq : (x + h) ^ (3 : ℝ) * (4 + 28125 / 2 * C_h) / (Real.pi * h * U) = K / U := by
    dsimp [K]
    rw [div_div]
  rw [h_eq] at h_bound
  refine h_bound.trans ?_
  rw [div_le_iff₀ hU_pos]
  have hK_le : K ≤ U * ε := (div_le_iff₀ hε).mp hKε_le_U
  linarith

/-- **Final `U`-Free Explicit Bound on `|Chebyshev.psi x - x|` via Contour Shift to `Re s = -1 /
4`**:
Combining the exact antiderivative bound on `Re s = -1 / 4`, the `O((log U) ^ 5 / U ^ 2)`
horizontal vanishing along zero-free heights `U → ∞`, and the multiplicity-weighted low/high
frequency Stieltjes bounds at `t₀ = 6` proves the complete `U`-independent explicit bound! -/
theorem abs_psi_sub_self_le_weighted_riemannVonMangoldt_six_neg_one_fourth
    (hRH : RiemannHypothesis) {x h T a_rvM C D A B C_h : ℝ}
    (hx_sub : 1 ≤ x - h) (hh : 0 < h) (h6T : 6 ≤ T)
    (ha_rvM : 0 ≤ a_rvM) (hD : 0 ≤ D)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hCh : 0 ≤ C_h)
    (hN_bound : ∀ t ≥ 6,
      (weightedZeroCountingFunction t : ℝ) ≤ a_rvM * t * Real.log t + C * t + D)
    (h_left_zeta : ∀ t : ℝ,
      ‖-deriv riemannZeta (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I) /
        riemannZeta (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ A * Real.log (|t| + 2) + B)
    (h_heights : ∀ U₀ ≥ T, ∃ U ≥ U₀,
      (∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) ∧
      (∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
        ‖-deriv riemannZeta ((σ : ℂ) + (U : ℂ) * I) /
          riemannZeta ((σ : ℂ) + (U : ℂ) * I)‖ ≤ C_h * (Real.log U) ^ 5) ∧
      (∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
        ‖-deriv riemannZeta ((σ : ℂ) - (U : ℂ) * I) /
          riemannZeta ((σ : ℂ) - (U : ℂ) * I)‖ ≤ C_h * (Real.log U) ^ 5)) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        Real.sqrt (x + h) *
          (a_rvM / 2 * (Real.log T) ^ 2 + (a_rvM + C) * Real.log T + C + D / 6 -
            a_rvM / 2 * (Real.log 6) ^ 2 - C * Real.log 6) +
        (2 * (x + h) ^ (3 / 2 : ℝ) / h) *
          ((2 * a_rvM * Real.log T + 2 * a_rvM + 2 * C) / T + 2 * D / T ^ 2) +
        32 * (2 * A + B) / (Real.pi * h) * (x + h) ^ (3 / 4 : ℝ) := by
  refine abs_psi_sub_self_le_weighted_riemannVonMangoldt_add_left_vertical
    hRH hx_sub hh (by norm_num : (0 : ℝ) < 6) h6T
    (by norm_num : (-1 / 2 : ℝ) < -1 / 4) (by norm_num : (-1 / 4 : ℝ) < 0)
    (weightedZeroCountingFunction_six_eq_zero hRH) ha_rvM hD hN_bound
    (fun U hTU ↦ contourLeftVerticalDiffError_neg_one_fourth_le hx_sub hh
      (by linarith : (0 : ℝ) ≤ U) hA hB h_left_zeta)
    (exists_zero_free_height_with_small_tailAndHorizontal hx_sub hh hCh h_heights)

end ConjectureMachines.Semantics.Riemann.WeightedStieltjes
