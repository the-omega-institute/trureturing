/- GID: D5/S3/Weil/Mertens/Cryptids/WeightedStieltjes/Foundation
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/Cryptids/WeightedStieltjes/Foundation
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

import D5.S3.Weil.Mertens.Cryptids.VonMangoldtCount
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Positivity
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.Positivity
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.RiemannZetaLogDeriv
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.ZetaZeros

/-! Original WeightedStieltjes analytic supplier for the RH Chebyshev estimate. -/

namespace ConjectureMachines.Semantics.Riemann.WeightedStieltjes

export ConjectureMachines.Semantics.Riemann.VonMangoldtCount
  (IsNontrivialZetaZero isNontrivialZetaZero_ne_zero re_lt_one_of_isNontrivialZetaZero zero_lt_re_of_isNontrivialZetaZero mem_criticalStrip_of_isNontrivialZetaZero
   finite_nontrivialZetaZeros_le nontrivialZetaZerosUpTo mem_nontrivialZetaZerosUpTo nontrivialZetaZerosBetween mem_nontrivialZetaZerosBetween
   filter_not_lt_abs_im_nontrivialZetaZerosUpTo sub_floor_bounds quartic_floor_bounds quarticKernel norm_quarticKernel_le_one_sixteenth
   measurable_quarticKernel locallyIntegrableOn_quarticKernel isBigO_quarticKernel_atTop isBigO_quarticKernel_nhdsGT_zero differentiableAt_mellin_quarticKernel
   mellin_quarticKernel_neg_add_three_eq sum_Icc_const_mul_pow_bounds LSeries_const_mul_pow_add_nat_eq integrableOn_floor_poly_mul_cpow integral_floor_poly_mul_cpow_eq
   sum_Icc_pow_zero sum_Icc_two_mul_pow_one sum_Icc_six_mul_pow_two sum_Icc_four_mul_pow_three integral_Ioi_one_cpow_neg_add_one
   mellin_quarticKernel_neg_add_three_eq_of_one_lt_re isPreconnected_re_pos sub_one_mul_mellin_quarticKernel_eq_of_re_pos mellin_quarticKernel_eq_of_riemannZeta_eq_zero quarticIocAntideriv
   hasDerivAt_quarticIocAntideriv integral_Ioc_one_two_quartic_le integral_Ioi_two_quartic_tail_le norm_mellin_quarticKernel_le_of_re_eq_half two_hundred_forty_le_norm_prod_of_riemannZeta_eq_zero_of_re_eq_half
   thirty_seven_lt_im_sq_of_riemannZeta_eq_zero_of_re_eq_half six_lt_abs_im_of_riemannZeta_eq_zero_of_re_eq_half six_lt_abs_im_of_riemannHypothesis nontrivialZetaZerosUpTo_eq_empty_of_le_six one_le_analyticOrderNatAt_of_isNontrivialZetaZero
   weightedZeroCountingFunction weightedZeroCountingFunction_eq_zero_of_le_six filter_abs_im_le_nontrivialZetaZerosBetween setIntegral_indicator_deriv_eq_sub integrableOn_indicator_of_continuousOn
   hasDerivAt_one_div intervalIntegral_riemannVonMangoldt_div_sq)

export RiemannSchmidt
  (analyticOrderAt_riemannZeta_ne_top)

open Complex Finset Filter MeasureTheory Set Asymptotics Topology
open scoped Real Topology Interval

open Real

/-- The integrated (smoothed) Chebyshev function $\psi_1(x) = \int_1^x \psi(t)\,dt$. -/
noncomputable def psi1 (x : ℝ) : ℝ :=
  ∫ t in (1 : ℝ)..x, Chebyshev.psi t

/-- For any `c t : ℝ`, the derivative of `x ↦ (x : ℂ) + (t : ℂ) * I` at `c` is `1`. -/
lemma hasDerivAt_ofReal_add_const_mul_I (c t : ℝ) :
    HasDerivAt (fun x : ℝ ↦ (x : ℂ) + (t : ℂ) * I) 1 c := by
  simpa using (Complex.ofRealCLM.hasDerivAt (x := c)).add_const ((t : ℂ) * I)

/-- For any `c t : ℝ`, the derivative of `y ↦ (c : ℂ) + (y : ℂ) * I` at `t` is `I`. -/
lemma hasDerivAt_const_add_ofReal_mul_I (c t : ℝ) :
    HasDerivAt (fun y : ℝ ↦ (c : ℂ) + (y : ℂ) * I) I t := by
  have h1 : HasDerivAt (fun y : ℝ ↦ (y : ℂ) * I) (1 * I) t :=
    (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I
  simpa using h1.const_add (c : ℂ)

/-- **1D FTC Rectangle Identity for Holomorphic Functions**:
If `F : ℂ → ℂ` is complex differentiable on an open set `U` containing the closed rectangle
`uIcc c₁ c₂ ×ℂ uIcc a b`, then the difference of the vertical integrals of `F` along `Re(s) = c₂`
and `Re(s) = c₁` from `t = a` to `t = b` equals `-I` times the horizontal integral of
`F(c + b * I) - F(c + a * I)` from `c = c₁` to `c = c₂`. -/
theorem vertical_integral_sub_eq_horizontal_integral {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {c₁ c₂ a b : ℝ}
    (h_mem : ∀ c ∈ uIcc c₁ c₂, ∀ t ∈ uIcc a b, (c : ℂ) + (t : ℂ) * I ∈ U) :
    (∫ t in a..b, F ((c₂ : ℂ) + (t : ℂ) * I)) - (∫ t in a..b, F ((c₁ : ℂ) + (t : ℂ) * I)) =
      -I * ∫ c in c₁..c₂, (F ((c : ℂ) + (b : ℂ) * I) - F ((c : ℂ) + (a : ℂ) * I)) := by
  have hF'_diff : DifferentiableOn ℂ (deriv F) U := hF.deriv hU
  have hF'_cont : ContinuousOn (deriv F) U := hF'_diff.continuousOn
  have h_map_cont : Continuous (fun p : ℝ × ℝ ↦ (p.1 : ℂ) + (p.2 : ℂ) * I) := by fun_prop
  have h_rect_cont : ContinuousOn (fun p : ℝ × ℝ ↦ deriv F ((p.1 : ℂ) + (p.2 : ℂ) * I))
      (uIcc c₁ c₂ ×ˢ uIcc a b) := by
    refine hF'_cont.comp h_map_cont.continuousOn ?_
    rintro ⟨c, t⟩ ⟨hc, ht⟩
    exact h_mem c hc t ht
  have h_rect_int : IntegrableOn (fun p : ℝ × ℝ ↦ deriv F ((p.1 : ℂ) + (p.2 : ℂ) * I))
      (uIoc c₁ c₂ ×ˢ uIoc a b) := by
    refine (h_rect_cont.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set ?_
    exact prod_mono uIoc_subset_uIcc uIoc_subset_uIcc
  have h_vert_int (c : ℝ) (hc : c ∈ uIcc c₁ c₂) :
      IntervalIntegrable (fun t : ℝ ↦ F ((c : ℂ) + (t : ℂ) * I)) volume a b := by
    refine (ContinuousOn.intervalIntegrable ?_)
    refine hF.continuousOn.comp (by fun_prop : Continuous fun t : ℝ ↦ (c : ℂ) +
      (t : ℂ) * I).continuousOn ?_
    intro t ht
    exact h_mem c hc t ht
  have h_ftc_c (t : ℝ) (ht : t ∈ uIcc a b) :
      ∫ c in c₁..c₂, deriv F ((c : ℂ) + (t : ℂ) * I) =
        F ((c₂ : ℂ) + (t : ℂ) * I) - F ((c₁ : ℂ) + (t : ℂ) * I) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro c hc
      have h_at : HasDerivAt F (deriv F ((c : ℂ) + (t : ℂ) * I)) ((c : ℂ) + (t : ℂ) * I) :=
        (hF.differentiableAt (hU.mem_nhds (h_mem c hc t ht))).hasDerivAt
      simpa [Function.comp_def] using h_at.scomp c (hasDerivAt_ofReal_add_const_mul_I c t)
    · refine ContinuousOn.intervalIntegrable ?_
      refine hF'_cont.comp (by fun_prop : Continuous fun c : ℝ ↦ (c : ℂ) +
        (t : ℂ) * I).continuousOn ?_
      intro c hc
      exact h_mem c hc t ht
  have h_ftc_t (c : ℝ) (hc : c ∈ uIcc c₁ c₂) :
      ∫ t in a..b, deriv F ((c : ℂ) + (t : ℂ) * I) =
        -I * (F ((c : ℂ) + (b : ℂ) * I) - F ((c : ℂ) + (a : ℂ) * I)) := by
    have h1 : ∫ t in a..b, I * deriv F ((c : ℂ) + (t : ℂ) * I) =
        F ((c : ℂ) + (b : ℂ) * I) - F ((c : ℂ) + (a : ℂ) * I) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro t ht
        have h_at : HasDerivAt F (deriv F ((c : ℂ) + (t : ℂ) * I)) ((c : ℂ) + (t : ℂ) * I) :=
          (hF.differentiableAt (hU.mem_nhds (h_mem c hc t ht))).hasDerivAt
        simpa [Function.comp_def, mul_comm] using
          h_at.scomp t (hasDerivAt_const_add_ofReal_mul_I c t)
      · refine ContinuousOn.intervalIntegrable ?_
        refine continuousOn_const.mul (hF'_cont.comp
          (by fun_prop : Continuous fun t : ℝ ↦ (c : ℂ) + (t : ℂ) * I).continuousOn ?_)
        intro t ht
        exact h_mem c hc t ht
    rw [intervalIntegral.integral_const_mul] at h1
    calc ∫ t in a..b, deriv F ((c : ℂ) + (t : ℂ) * I)
        = (-I * I) * ∫ t in a..b, deriv F ((c : ℂ) + (t : ℂ) * I) := by simp
      _ = -I * (I * ∫ t in a..b, deriv F ((c : ℂ) + (t : ℂ) * I)) := by ring
      _ = -I * (F ((c : ℂ) + (b : ℂ) * I) - F ((c : ℂ) + (a : ℂ) * I)) := by rw [h1]
  calc (∫ t in a..b, F ((c₂ : ℂ) + (t : ℂ) * I)) - (∫ t in a..b, F ((c₁ : ℂ) + (t : ℂ) * I))
      = ∫ t in a..b, (F ((c₂ : ℂ) + (t : ℂ) * I) - F ((c₁ : ℂ) + (t : ℂ) * I)) := by
        rw [intervalIntegral.integral_sub (h_vert_int c₂ right_mem_uIcc)
          (h_vert_int c₁ left_mem_uIcc)]
    _ = ∫ t in a..b, ∫ c in c₁..c₂, deriv F ((c : ℂ) + (t : ℂ) * I) := by
        refine intervalIntegral.integral_congr fun t ht ↦ (h_ftc_c t ht).symm
    _ = ∫ c in c₁..c₂, ∫ t in a..b, deriv F ((c : ℂ) + (t : ℂ) * I) := by
        exact (intervalIntegral_intervalIntegral_swap
          (F := fun c t : ℝ ↦ deriv F ((c : ℂ) + (t : ℂ) * I)) h_rect_int).symm
    _ = ∫ c in c₁..c₂, -I * (F ((c : ℂ) + (b : ℂ) * I) - F ((c : ℂ) + (a : ℂ) * I)) := by
        refine intervalIntegral.integral_congr fun c hc ↦ h_ftc_t c hc
    _ = -I * ∫ c in c₁..c₂, (F ((c : ℂ) + (b : ℂ) * I) - F ((c : ℂ) + (a : ℂ) * I)) := by
        rw [intervalIntegral.integral_const_mul]

/-- Bound on the difference of truncated vertical integrals in terms of horizontal segment bounds.
-/
theorem norm_vertical_integral_sub_le {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {c₁ c₂ a b M_a M_b : ℝ}
    (h_mem : ∀ c ∈ uIcc c₁ c₂, ∀ t ∈ uIcc a b, (c : ℂ) + (t : ℂ) * I ∈ U)
    (hMa : ∀ c ∈ uIcc c₁ c₂, ‖F ((c : ℂ) + (a : ℂ) * I)‖ ≤ M_a)
    (hMb : ∀ c ∈ uIcc c₁ c₂, ‖F ((c : ℂ) + (b : ℂ) * I)‖ ≤ M_b) :
    ‖(∫ t in a..b, F ((c₂ : ℂ) + (t : ℂ) * I)) - (∫ t in a..b, F ((c₁ : ℂ) + (t : ℂ) * I))‖ ≤
      (M_b + M_a) * |c₂ - c₁| := by
  rw [vertical_integral_sub_eq_horizontal_integral hU hF h_mem, norm_mul, norm_neg,
    Complex.norm_I, one_mul]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun c hc ↦ ?_
  have hc' : c ∈ uIcc c₁ c₂ := uIoc_subset_uIcc hc
  calc ‖F ((c : ℂ) + (b : ℂ) * I) - F ((c : ℂ) + (a : ℂ) * I)‖
      ≤ ‖F ((c : ℂ) + (b : ℂ) * I)‖ + ‖F ((c : ℂ) + (a : ℂ) * I)‖ := norm_sub_le _ _
    _ ≤ M_b + M_a := add_le_add (hMb c hc') (hMa c hc')

/-- **Improper Vertical Integral Shift Theorem**:
If `F : ℂ → ℂ` is complex differentiable on an open set `U` containing the closed strip
`{s : ℂ | s.re ∈ uIcc c₁ c₂}`, is integrable along both vertical lines `Re(s) = c₁` and
`Re(s) = c₂`, and `sup_{c ∈ uIcc c₁ c₂} ‖F(c ± T*I)‖ → 0` as `T → ∞`, then the improper vertical
integrals along `Re(s) = c₁` and `Re(s) = c₂` are equal. -/
theorem integral_vertical_eq_of_differentiableOn_strip {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {c₁ c₂ : ℝ}
    (h_mem : ∀ c ∈ uIcc c₁ c₂, ∀ t : ℝ, (c : ℂ) + (t : ℂ) * I ∈ U)
    (h_int₁ : Integrable (fun t : ℝ ↦ F ((c₁ : ℂ) + (t : ℂ) * I)))
    (h_int₂ : Integrable (fun t : ℝ ↦ F ((c₂ : ℂ) + (t : ℂ) * I)))
    {B : ℝ → ℝ} (hB_tendsto : Tendsto B atTop (𝓝 0))
    (hB_top : ∀ᶠ T : ℝ in atTop, ∀ c ∈ uIcc c₁ c₂, ‖F ((c : ℂ) + (T : ℂ) * I)‖ ≤ B T)
    (hB_bot : ∀ᶠ T : ℝ in atTop, ∀ c ∈ uIcc c₁ c₂, ‖F ((c : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ B T) :
    (∫ t : ℝ, F ((c₂ : ℂ) + (t : ℂ) * I)) = ∫ t : ℝ, F ((c₁ : ℂ) + (t : ℂ) * I) := by
  have h_lim₁ : Tendsto (fun T : ℝ ↦ ∫ t in (-T)..T, F ((c₁ : ℂ) + (t : ℂ) * I))
      atTop (𝓝 (∫ t : ℝ, F ((c₁ : ℂ) + (t : ℂ) * I))) :=
    intervalIntegral_tendsto_integral h_int₁ tendsto_neg_atTop_atBot tendsto_id
  have h_lim₂ : Tendsto (fun T : ℝ ↦ ∫ t in (-T)..T, F ((c₂ : ℂ) + (t : ℂ) * I))
      atTop (𝓝 (∫ t : ℝ, F ((c₂ : ℂ) + (t : ℂ) * I))) :=
    intervalIntegral_tendsto_integral h_int₂ tendsto_neg_atTop_atBot tendsto_id
  have h_diff_lim : Tendsto (fun T : ℝ ↦
      (∫ t in (-T)..T, F ((c₂ : ℂ) + (t : ℂ) * I)) -
      (∫ t in (-T)..T, F ((c₁ : ℂ) + (t : ℂ) * I)))
      atTop (𝓝 ((∫ t : ℝ, F ((c₂ : ℂ) + (t : ℂ) * I)) - ∫ t : ℝ, F ((c₁ : ℂ) + (t : ℂ) * I))) :=
    h_lim₂.sub h_lim₁
  have h_diff_zero : Tendsto (fun T : ℝ ↦
      (∫ t in (-T)..T, F ((c₂ : ℂ) + (t : ℂ) * I)) -
      (∫ t in (-T)..T, F ((c₁ : ℂ) + (t : ℂ) * I))) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using (hB_tendsto.add hB_tendsto).mul_const |c₂ - c₁|)
    filter_upwards [hB_top, hB_bot] with T hT_top hT_bot
    exact norm_vertical_integral_sub_le hU hF (fun c hc t _ ↦ h_mem c hc t) hT_bot hT_top
  exact sub_eq_zero.mp (tendsto_nhds_unique h_diff_lim h_diff_zero)

/-!
# Section 2A: Basic Norm Bounds, Pole-Pair Integral, and the `0 < y ≤ 1` Case
-/

lemma re_ofReal_add_ofReal_mul_I (c t : ℝ) : ((c : ℂ) + (t : ℂ) * I).re = c := by
  simp

lemma norm_sq_ofReal_add_ofReal_mul_I (c t : ℝ) :
    ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2 = c ^ 2 + t ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [sq]

lemma norm_ofReal_add_ofReal_mul_I_ge_abs_im (c t : ℝ) :
    |t| ≤ ‖(c : ℂ) + (t : ℂ) * I‖ := by
  simpa using Complex.abs_im_le_norm ((c : ℂ) + (t : ℂ) * I)

lemma ofReal_add_ofReal_mul_I_ne_zero_of_re_ne_zero {c t : ℝ} (hc : c ≠ 0) :
    (c : ℂ) + (t : ℂ) * I ≠ 0 := by
  intro h
  have hre := congr_arg Complex.re h
  exact hc (by simpa using hre)

lemma ofReal_add_ofReal_mul_I_ne_zero_of_im_ne_zero {c t : ℝ} (ht : t ≠ 0) :
    (c : ℂ) + (t : ℂ) * I ≠ 0 := by
  intro h
  have him := congr_arg Complex.im h
  exact ht (by simpa using him)

/-- For any `c ≠ 0`, `t ↦ (c ^ 2 + t ^ 2)⁻¹` is integrable on `ℝ`. -/
lemma integrable_inv_sq_add_sq {c : ℝ} (hc : c ≠ 0) :
    Integrable (fun t : ℝ ↦ (c ^ 2 + t ^ 2)⁻¹) := by
  have h_eq : (fun t : ℝ ↦ (c ^ 2 + t ^ 2)⁻¹) =
      fun t : ℝ ↦ (c ^ 2)⁻¹ * (1 + (c⁻¹ * t) ^ 2)⁻¹ := by
    ext t
    have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
    field_simp
  rw [h_eq]
  exact (integrable_inv_one_add_mul_sq (inv_ne_zero hc)).const_mul (c ^ 2)⁻¹

/-- For any `c ≠ 0`, `∫ t : ℝ, (c ^ 2 + t ^ 2)⁻¹ = π / |c|`. -/
lemma integral_inv_sq_add_sq {c : ℝ} (hc : c ≠ 0) :
    (∫ t : ℝ, (c ^ 2 + t ^ 2)⁻¹) = π / |c| := by
  have h_eq : (fun t : ℝ ↦ (c ^ 2 + t ^ 2)⁻¹) =
      fun t : ℝ ↦ (c ^ 2)⁻¹ * (1 + (c⁻¹ * t) ^ 2)⁻¹ := by
    ext t
    have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
    field_simp
  rw [h_eq, integral_const_mul, integral_univ_inv_one_add_mul_sq, abs_inv, div_inv_eq_mul]
  have h_abs : c ^ 2 = |c| ^ 2 := (sq_abs c).symm
  have h_abs_ne : |c| ≠ 0 := abs_ne_zero.mpr hc
  rw [h_abs]
  field_simp

/-- Algebraic decomposition of `((a : ℂ) + t * I)⁻¹` into real and imaginary parts. -/
lemma inv_ofReal_add_ofReal_mul_I_eq {a t : ℝ} (ha : a ≠ 0) :
    ((a : ℂ) + (t : ℂ) * I)⁻¹ =
      ((a / (a ^ 2 + t ^ 2) : ℝ) : ℂ) - ((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * I := by
  have h_ne : (a : ℂ) + (t : ℂ) * I ≠ 0 := ofReal_add_ofReal_mul_I_ne_zero_of_re_ne_zero ha
  have h_sq_pos : 0 < a ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha) (sq_nonneg t)
  have h_sq_ne : (a : ℂ) ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast h_sq_pos.ne'
  apply mul_left_cancel₀ h_ne
  rw [mul_inv_cancel₀ h_ne]
  symm
  push_cast
  have hI : I ^ 2 = -1 := I_sq
  calc ((a : ℂ) + (t : ℂ) * I) *
        ((a : ℂ) / ((a : ℂ) ^ 2 + (t : ℂ) ^ 2) - (t : ℂ) / ((a : ℂ) ^ 2 + (t : ℂ) ^ 2) * I)
      = ((a : ℂ) ^ 2 - (t : ℂ) ^ 2 * I ^ 2) / ((a : ℂ) ^ 2 + (t : ℂ) ^ 2) := by ring
    _ = ((a : ℂ) ^ 2 + (t : ℂ) ^ 2) / ((a : ℂ) ^ 2 + (t : ℂ) ^ 2) := by rw [hI]; ring
    _ = 1 := div_self h_sq_ne

/-- Integrability of the odd imaginary part `t ↦ t / (a^2 + t^2) - t / (b^2 + t^2)` for `a, b ≠ 0`.
-/
lemma integrable_im_pole_pair {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Integrable (fun t : ℝ ↦ t / (a ^ 2 + t ^ 2) - t / (b ^ 2 + t ^ 2)) := by
  refine ((integrable_inv_sq_add_sq hb).const_mul (|b ^ 2 - a ^ 2| / (2 * |a|))).mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    have ha_ne : ∀ t : ℝ, a ^ 2 + t ^ 2 ≠ 0 := fun t ↦
      (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha) (sq_nonneg t)).ne'
    have hb_ne : ∀ t : ℝ, b ^ 2 + t ^ 2 ≠ 0 := fun t ↦
      (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hb) (sq_nonneg t)).ne'
    fun_prop (disch := assumption)
  · filter_upwards with t
    have ha_pos : 0 < a ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha) (sq_nonneg t)
    have hb_pos : 0 < b ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hb) (sq_nonneg t)
    have h_diff : t / (a ^ 2 + t ^ 2) - t / (b ^ 2 + t ^ 2) =
        (b ^ 2 - a ^ 2) * t / ((a ^ 2 + t ^ 2) * (b ^ 2 + t ^ 2)) := by
      field_simp
      ring
    rw [h_diff, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (mul_pos ha_pos hb_pos)]
    have h_amgm : 2 * |a| * |t| ≤ a ^ 2 + t ^ 2 := by
      have hsq : 0 ≤ (|a| - |t|) ^ 2 := sq_nonneg _
      linarith [sq_abs a, sq_abs t]
    have h_t_le : |t| / (a ^ 2 + t ^ 2) ≤ 1 / (2 * |a|) := by
      rw [div_le_div_iff₀ ha_pos (by positivity)]
      linarith
    calc |b ^ 2 - a ^ 2| * |t| / ((a ^ 2 + t ^ 2) * (b ^ 2 + t ^ 2))
        = |b ^ 2 - a ^ 2| * (|t| / (a ^ 2 + t ^ 2)) * (b ^ 2 + t ^ 2)⁻¹ := by
          field_simp
      _ ≤ |b ^ 2 - a ^ 2| * (1 / (2 * |a|)) * (b ^ 2 + t ^ 2)⁻¹ := by
          gcongr
      _ = |b ^ 2 - a ^ 2| / (2 * |a|) * (b ^ 2 + t ^ 2)⁻¹ := by ring

/-- The integral of the odd imaginary part `t ↦ t / (a^2 + t^2) - t / (b^2 + t^2)` is `0`. -/
lemma integral_im_pole_pair {a b : ℝ} :
    (∫ t : ℝ, (t / (a ^ 2 + t ^ 2) - t / (b ^ 2 + t ^ 2))) = 0 := by
  let f : ℝ → ℝ := fun t ↦ t / (a ^ 2 + t ^ 2) - t / (b ^ 2 + t ^ 2)
  have h_odd : ∀ t : ℝ, f (-t) = -f t := by
    intro t
    dsimp [f]
    ring
  have h_emb : MeasurableEmbedding (fun x : ℝ ↦ -x) :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  have h_comp_neg : (∫ t : ℝ, f (-t)) = ∫ t : ℝ, f t := by
    have h1 := h_emb.integral_map (μ := volume) f
    rw [Measure.map_neg_eq_self (volume : Measure ℝ)] at h1
    exact h1.symm
  have h_int : (∫ t : ℝ, f t) = -(∫ t : ℝ, f t) := by
    calc (∫ t : ℝ, f t) = ∫ t : ℝ, f (-t) := h_comp_neg.symm
      _ = ∫ t : ℝ, -f t := by simp_rw [h_odd]
      _ = -(∫ t : ℝ, f t) := integral_neg f
  linarith

/-- For `a ≠ 0` and `b ≠ 0`, `t ↦ ((a : ℂ) + t * I)⁻¹ - ((b : ℂ) + t * I)⁻¹` is integrable on `ℝ`.
-/
lemma integrable_inv_sub_inv_ofReal_add_ofReal_mul_I {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Integrable (fun t : ℝ ↦ ((a : ℂ) + (t : ℂ) * I)⁻¹ - ((b : ℂ) + (t : ℂ) * I)⁻¹) := by
  have h_eq : (fun t : ℝ ↦ ((a : ℂ) + (t : ℂ) * I)⁻¹ - ((b : ℂ) + (t : ℂ) * I)⁻¹) =
      fun t : ℝ ↦ (((a / (a ^ 2 + t ^ 2) - b / (b ^ 2 + t ^ 2) : ℝ) : ℂ) -
        ((t / (a ^ 2 + t ^ 2) - t / (b ^ 2 + t ^ 2) : ℝ) : ℂ) * I) := by
    ext t
    rw [inv_ofReal_add_ofReal_mul_I_eq ha, inv_ofReal_add_ofReal_mul_I_eq hb]
    push_cast
    ring
  rw [h_eq]
  have h_re : Integrable (fun t : ℝ ↦ a / (a ^ 2 + t ^ 2) - b / (b ^ 2 + t ^ 2)) := by
    simp_rw [div_eq_mul_inv]
    exact Integrable.sub ((integrable_inv_sq_add_sq ha).const_mul a)
      ((integrable_inv_sq_add_sq hb).const_mul b)
  exact Integrable.sub h_re.ofReal ((integrable_im_pole_pair ha hb).ofReal.mul_const I)

/-- **Pole-Pair Integral Formula**:
For `b < 0 < a`, `∫ t : ℝ, (((a : ℂ) + t * I)⁻¹ - ((b : ℂ) + t * I)⁻¹) = 2 * π`. -/
theorem integral_inv_sub_inv_ofReal_add_ofReal_mul_I {a b : ℝ} (ha : 0 < a) (hb : b < 0) :
    (∫ t : ℝ, (((a : ℂ) + (t : ℂ) * I)⁻¹ - ((b : ℂ) + (t : ℂ) * I)⁻¹)) = 2 * π := by
  have h_eq : (fun t : ℝ ↦ ((a : ℂ) + (t : ℂ) * I)⁻¹ - ((b : ℂ) + (t : ℂ) * I)⁻¹) =
      fun t : ℝ ↦ (((a / (a ^ 2 + t ^ 2) - b / (b ^ 2 + t ^ 2) : ℝ) : ℂ) -
        ((t / (a ^ 2 + t ^ 2) - t / (b ^ 2 + t ^ 2) : ℝ) : ℂ) * I) := by
    ext t
    rw [inv_ofReal_add_ofReal_mul_I_eq ha.ne', inv_ofReal_add_ofReal_mul_I_eq hb.ne]
    push_cast
    ring
  have h_re_int : Integrable (fun t : ℝ ↦ a * (a ^ 2 + t ^ 2)⁻¹) :=
    (integrable_inv_sq_add_sq ha.ne').const_mul a
  have h_re_int' : Integrable (fun t : ℝ ↦ b * (b ^ 2 + t ^ 2)⁻¹) :=
    (integrable_inv_sq_add_sq hb.ne).const_mul b
  have h_re_diff : Integrable (fun t : ℝ ↦ a / (a ^ 2 + t ^ 2) - b / (b ^ 2 + t ^ 2)) := by
    simp_rw [div_eq_mul_inv]
    exact Integrable.sub h_re_int h_re_int'
  have h_re_c : Integrable (fun t : ℝ ↦ ((a / (a ^ 2 + t ^ 2) - b / (b ^ 2 + t ^ 2) : ℝ) : ℂ)) :=
    h_re_diff.ofReal
  have h_im_c : Integrable (fun t : ℝ ↦
      ((t / (a ^ 2 + t ^ 2) - t / (b ^ 2 + t ^ 2) : ℝ) : ℂ) * I) :=
    (integrable_im_pole_pair ha.ne' hb.ne).ofReal.mul_const I
  have h_re_ofReal : (∫ t : ℝ, ((a / (a ^ 2 + t ^ 2) - b / (b ^ 2 + t ^ 2) : ℝ) : ℂ)) =
      ((∫ t : ℝ, (a / (a ^ 2 + t ^ 2) - b / (b ^ 2 + t ^ 2)) : ℝ) : ℂ) :=
    Complex.ofRealCLM.integral_comp_comm h_re_diff
  have h_im_ofReal : (∫ t : ℝ, ((t / (a ^ 2 + t ^ 2) - t / (b ^ 2 + t ^ 2) : ℝ) : ℂ)) =
      ((∫ t : ℝ, (t / (a ^ 2 + t ^ 2) - t / (b ^ 2 + t ^ 2)) : ℝ) : ℂ) :=
    Complex.ofRealCLM.integral_comp_comm (integrable_im_pole_pair ha.ne' hb.ne)
  rw [h_eq, integral_sub h_re_c h_im_c]
  rw [integral_mul_const, h_im_ofReal, integral_im_pole_pair, Complex.ofReal_zero,
    zero_mul, sub_zero, h_re_ofReal]
  have h_re_eval : (∫ t : ℝ, (a / (a ^ 2 + t ^ 2) - b / (b ^ 2 + t ^ 2))) = 2 * π := by
    simp_rw [div_eq_mul_inv]
    rw [integral_sub h_re_int h_re_int', integral_const_mul, integral_const_mul,
      integral_inv_sq_add_sq ha.ne', integral_inv_sq_add_sq hb.ne,
      abs_of_pos ha, abs_of_neg hb]
    have ha_ne : a ≠ 0 := ha.ne'
    have hb_ne : b ≠ 0 := hb.ne
    field_simp
    ring
  rw [h_re_eval]
  push_cast
  ring

/-- The smoothed Perron integrand `s ↦ y ^ (s + 1) / (s * (s + 1))`. -/
noncomputable def smoothedPerronKernel (y : ℝ) (s : ℂ) : ℂ :=
  (y : ℂ) ^ (s + 1) / (s * (s + 1))

/-- For `0 < y`, `z ↦ (y : ℂ) ^ (z + 1)` is differentiable on all of `ℂ`. -/
lemma differentiable_ofReal_cpow_add_one {y : ℝ} (hy : 0 < y) :
    Differentiable ℂ (fun z : ℂ ↦ (y : ℂ) ^ (z + 1)) := by
  intro z
  exact (differentiableAt_id.add_const 1).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))

/-- For `0 < y`, `smoothedPerronKernel y` is differentiable on `{s : ℂ | s ≠ 0 ∧ s + 1 ≠ 0}`. -/
lemma differentiableOn_smoothedPerronKernel {y : ℝ} (hy : 0 < y) :
    DifferentiableOn ℂ (smoothedPerronKernel y) {s : ℂ | s ≠ 0 ∧ s + 1 ≠ 0} := by
  intro s hs
  refine ((differentiable_ofReal_cpow_add_one hy s).div
    (differentiableAt_id.mul (differentiableAt_id.add_const 1))
    (mul_ne_zero hs.1 hs.2)).differentiableWithinAt

/-- Pointwise norm bound on `smoothedPerronKernel y (c + t * I)` for `0 < y` and `0 < c`. -/
lemma norm_smoothedPerronKernel_le {y c : ℝ} (hy : 0 < y) (hc : 0 < c) (t : ℝ) :
    ‖smoothedPerronKernel y ((c : ℂ) + (t : ℂ) * I)‖ ≤
      y ^ (c + 1) * (c ^ 2 + t ^ 2)⁻¹ := by
  dsimp [smoothedPerronKernel]
  rw [norm_div, norm_mul]
  have h_num : ‖(y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I + 1)‖ = y ^ (c + 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
    simp
  rw [h_num]
  have h_den : c ^ 2 + t ^ 2 ≤
      ‖(c : ℂ) + (t : ℂ) * I‖ * ‖(c : ℂ) + (t : ℂ) * I + 1‖ := by
    have h1 : c ^ 2 + t ^ 2 = ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2 :=
      (norm_sq_ofReal_add_ofReal_mul_I c t).symm
    have h2 : ‖(c : ℂ) + (t : ℂ) * I‖ ≤ ‖(c : ℂ) + (t : ℂ) * I + 1‖ := by
      have h_eq : (c : ℂ) + (t : ℂ) * I + 1 = ((c + 1 : ℝ) : ℂ) + (t : ℂ) * I := by
        push_cast; ring
      rw [h_eq, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
        norm_sq_ofReal_add_ofReal_mul_I, norm_sq_ofReal_add_ofReal_mul_I]
      nlinarith
    rw [h1, sq]
    exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  have hc_pos : 0 < c ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (sq_nonneg t)
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (inv_anti₀ hc_pos h_den) (rpow_nonneg hy.le _)

/-- For `0 < y` and `0 < c`, `t ↦ smoothedPerronKernel y (c + t * I)` is integrable on `ℝ`. -/
theorem integrable_smoothedPerronKernel {y c : ℝ} (hy : 0 < y) (hc : 0 < c) :
    Integrable (fun t : ℝ ↦ smoothedPerronKernel y ((c : ℂ) + (t : ℂ) * I)) := by
  refine ((integrable_inv_sq_add_sq hc.ne').const_mul (y ^ (c + 1))).mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    have h_cont : Continuous (fun t : ℝ ↦ (c : ℂ) + (t : ℂ) * I) := by fun_prop
    refine (differentiableOn_smoothedPerronKernel hy).continuousOn.comp_continuous h_cont
      fun t ↦ ⟨ofReal_add_ofReal_mul_I_ne_zero_of_re_ne_zero hc.ne', ?_⟩
    have h_eq : (c : ℂ) + (t : ℂ) * I + 1 = ((c + 1 : ℝ) : ℂ) + (t : ℂ) * I := by
      push_cast; ring
    rw [h_eq]
    exact ofReal_add_ofReal_mul_I_ne_zero_of_re_ne_zero (by linarith)
  · filter_upwards with t
    exact norm_smoothedPerronKernel_le hy hc t

/-- Helper bound for `y ^ (c + 1)` when `c ∈ uIcc c₁ c₂`. -/
lemma rpow_add_one_le_max_of_mem_uIcc {y c₁ c₂ c : ℝ} (hy : 0 < y) (hc : c ∈ uIcc c₁ c₂) :
    y ^ (c + 1) ≤ max (y ^ (c₁ + 1)) (y ^ (c₂ + 1)) := by
  have hc_min : min c₁ c₂ ≤ c := hc.1
  have hc_max : c ≤ max c₁ c₂ := hc.2
  rcases le_or_gt y 1 with hy1 | hy1
  · have h1 : y ^ (c + 1) ≤ y ^ (min c₁ c₂ + 1) :=
      Real.rpow_le_rpow_of_exponent_ge hy hy1 (by linarith)
    refine h1.trans ?_
    rcases min_cases c₁ c₂ with ⟨hmin, _⟩ | ⟨hmin, _⟩ <;> rw [hmin]
    · exact le_max_left _ _
    · exact le_max_right _ _
  · have h1 : y ^ (c + 1) ≤ y ^ (max c₁ c₂ + 1) :=
      Real.rpow_le_rpow_of_exponent_le hy1.le (by linarith)
    refine h1.trans ?_
    rcases max_cases c₁ c₂ with ⟨hmax, _⟩ | ⟨hmax, _⟩ <;> rw [hmax]
    · exact le_max_left _ _
    · exact le_max_right _ _

/-- Shifting the vertical line `Re(s) = c` for `smoothedPerronKernel y` when `c₁, c₂ > 0`. -/
theorem integral_smoothedPerronKernel_eq_of_pos {y c₁ c₂ : ℝ} (hy : 0 < y)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    (∫ t : ℝ, smoothedPerronKernel y ((c₂ : ℂ) + (t : ℂ) * I)) =
      ∫ t : ℝ, smoothedPerronKernel y ((c₁ : ℂ) + (t : ℂ) * I) := by
  let U : Set ℂ := {s : ℂ | 0 < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hF : DifferentiableOn ℂ (smoothedPerronKernel y) U := by
    refine (differentiableOn_smoothedPerronKernel hy).mono fun s hs ↦ ⟨?_, ?_⟩
    · intro h0
      have hs_pos : 0 < s.re := hs
      rw [h0, Complex.zero_re] at hs_pos
      exact lt_irrefl 0 hs_pos
    · intro h1
      have hre : (s + 1).re = 0 := by rw [h1, Complex.zero_re]
      simp only [Complex.add_re, Complex.one_re] at hre
      have hs_pos : 0 < s.re := hs
      linarith
  let M : ℝ := max (y ^ (c₁ + 1)) (y ^ (c₂ + 1))
  refine integral_vertical_eq_of_differentiableOn_strip hU hF
    (fun c hc t ↦ ?_) (integrable_smoothedPerronKernel hy hc₁)
    (integrable_smoothedPerronKernel hy hc₂)
    (B := fun T : ℝ ↦ M * (T ^ 2)⁻¹) ?_ ?_ ?_
  · change 0 < ((c : ℂ) + (t : ℂ) * I).re
    rw [re_ofReal_add_ofReal_mul_I]
    exact lt_of_lt_of_le (lt_min hc₁ hc₂) hc.1
  · have h_tendsto : Tendsto (fun T : ℝ ↦ (T ^ 2)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
    simpa using h_tendsto.const_mul M
  · filter_upwards [eventually_gt_atTop 0] with T hT c hc
    have hc_pos : 0 < c := lt_of_lt_of_le (lt_min hc₁ hc₂) hc.1
    have h_le := norm_smoothedPerronKernel_le hy hc_pos T
    have h_yc : y ^ (c + 1) ≤ M := rpow_add_one_le_max_of_mem_uIcc hy hc
    have h_inv : (c ^ 2 + T ^ 2)⁻¹ ≤ (T ^ 2)⁻¹ :=
      inv_anti₀ (sq_pos_of_pos hT) (by nlinarith)
    exact h_le.trans (mul_le_mul h_yc h_inv (by positivity) (by positivity))
  · filter_upwards [eventually_gt_atTop 0] with T hT c hc
    have hc_pos : 0 < c := lt_of_lt_of_le (lt_min hc₁ hc₂) hc.1
    have h_le := norm_smoothedPerronKernel_le hy hc_pos (-T)
    rw [neg_sq] at h_le
    have h_yc : y ^ (c + 1) ≤ M := rpow_add_one_le_max_of_mem_uIcc hy hc
    have h_inv : (c ^ 2 + T ^ 2)⁻¹ ≤ (T ^ 2)⁻¹ :=
      inv_anti₀ (sq_pos_of_pos hT) (by nlinarith)
    exact h_le.trans (mul_le_mul h_yc h_inv (by positivity) (by positivity))

/-- **Smoothed Perron Formula for `0 < y ≤ 1`**:
When `0 < y ≤ 1` and `0 < c`, the vertical integral of `smoothedPerronKernel y` vanishes. -/
theorem integral_smoothedPerronKernel_eq_zero_of_le_one {y c : ℝ} (hy : 0 < y) (hy1 : y ≤ 1)
    (hc : 0 < c) :
    (∫ t : ℝ, smoothedPerronKernel y ((c : ℂ) + (t : ℂ) * I)) = 0 := by
  have h_bound : ∀ C : ℝ, 0 < C →
      ‖∫ t : ℝ, smoothedPerronKernel y ((c : ℂ) + (t : ℂ) * I)‖ ≤ π / C := by
    intro C hC
    rw [← integral_smoothedPerronKernel_eq_of_pos hy hc hC]
    calc ‖∫ t : ℝ, smoothedPerronKernel y ((C : ℂ) + (t : ℂ) * I)‖
        ≤ ∫ t : ℝ, ‖smoothedPerronKernel y ((C : ℂ) + (t : ℂ) * I)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, y ^ (C + 1) * (C ^ 2 + t ^ 2)⁻¹ := by
          refine integral_mono (integrable_smoothedPerronKernel hy hC).norm
            ((integrable_inv_sq_add_sq hC.ne').const_mul _) (norm_smoothedPerronKernel_le hy hC)
      _ = y ^ (C + 1) * (π / |C|) := by
          rw [integral_const_mul, integral_inv_sq_add_sq hC.ne']
      _ ≤ 1 * (π / C) := by
          rw [abs_of_pos hC]
          gcongr
          exact Real.rpow_le_one hy.le hy1 (by linarith)
      _ = π / C := one_mul _
  have h_tendsto : Tendsto (fun C : ℝ ↦ π / C) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul π
  have h_norm_le : ‖∫ t : ℝ, smoothedPerronKernel y ((c : ℂ) + (t : ℂ) * I)‖ ≤ 0 := by
    refine ge_of_tendsto h_tendsto ?_
    filter_upwards [eventually_gt_atTop 0] with C hC
    exact h_bound C hC
  exact norm_le_zero_iff.mp h_norm_le

/-!
# Section 2B: Removable-Singularity Pole Subtraction and the `y ≥ 1` Case
-/

/-- The pole-subtracted auxiliary function for `y > 0`, defined globally via `dslope` at `0` and
`-1`
so that its removable singularities at `s = 0` and `s = -1` are automatically resolved. -/
noncomputable def perronAux (y : ℝ) (s : ℂ) : ℂ :=
  dslope (fun z : ℂ ↦ (y : ℂ) ^ (z + 1)) 0 s -
  dslope (fun z : ℂ ↦ (y : ℂ) ^ (z + 1)) (-1) s +
  ((y : ℂ) - 1) / (s - 1)

/-- For `0 < y`, `perronAux y` is complex differentiable on the entire half-plane `{s : ℂ | s.re <
1}`. -/
lemma differentiableOn_perronAux {y : ℝ} (hy : 0 < y) :
    DifferentiableOn ℂ (perronAux y) {s : ℂ | s.re < 1} := by
  have h_ent : DifferentiableOn ℂ (fun z : ℂ ↦ (y : ℂ) ^ (z + 1)) univ :=
    (differentiable_ofReal_cpow_add_one hy).differentiableOn
  have hd0 : DifferentiableOn ℂ (dslope (fun z : ℂ ↦ (y : ℂ) ^ (z + 1)) 0) univ :=
    (Complex.differentiableOn_dslope univ_mem).mpr h_ent
  have hd1 : DifferentiableOn ℂ (dslope (fun z : ℂ ↦ (y : ℂ) ^ (z + 1)) (-1)) univ :=
    (Complex.differentiableOn_dslope univ_mem).mpr h_ent
  have h_div : DifferentiableOn ℂ (fun s : ℂ ↦ ((y : ℂ) - 1) / (s - 1)) {s : ℂ | s.re < 1} := by
    intro s hs
    refine ((differentiableAt_const _).div (differentiableAt_id.sub_const 1)
      ?_).differentiableWithinAt
    intro h_eq
    have hre : (s - 1).re = 0 := by rw [h_eq, Complex.zero_re]
    simp only [Complex.sub_re, Complex.one_re] at hre
    have hs_lt : s.re < 1 := hs
    linarith
  exact ((hd0.mono (subset_univ _)).sub (hd1.mono (subset_univ _))).add h_div

/-- **Form A of `perronAux`**: Away from `s = 0` and `s = -1`, `perronAux y s` is the smoothed
Perron
integrand minus the pole pairs at `(0, 1)` and `(-1, 1)`. -/
lemma perronAux_eq_pole_sub {y : ℝ} {s : ℂ} (hs0 : s ≠ 0) (hs_add1 : s + 1 ≠ 0) :
    perronAux y s =
      smoothedPerronKernel y s - (y : ℂ) * (s⁻¹ - (s - 1)⁻¹) + ((s + 1)⁻¹ - (s - 1)⁻¹) := by
  have hs_neg1 : s ≠ -1 := fun h ↦ hs_add1 (by rw [h]; ring)
  unfold perronAux smoothedPerronKernel
  rw [dslope_of_ne _ hs0, dslope_of_ne _ hs_neg1, slope_def_field, slope_def_field]
  simp only [zero_add, Complex.cpow_one, neg_add_cancel, Complex.cpow_zero, sub_zero,
    sub_neg_eq_add]
  field_simp [hs0, hs_add1]
  ring

/-- **Form B of `perronAux`**: Away from `s = 0, -1, 1`, `perronAux y s` is a sum of three terms
each
decaying quadratically as `|s| → ∞`. -/
lemma perronAux_eq_quad_decay {y : ℝ} {s : ℂ} (hs0 : s ≠ 0) (hs_add1 : s + 1 ≠ 0)
    (hs_sub1 : s - 1 ≠ 0) :
    perronAux y s =
      smoothedPerronKernel y s + (y : ℂ) / (s * (s - 1)) - 2 / ((s + 1) * (s - 1)) := by
  rw [perronAux_eq_pole_sub hs0 hs_add1]
  field_simp [hs0, hs_add1, hs_sub1]
  ring

/-- Horizontal segment bound for `perronAux y (c + T * I)` when `T ≠ 0`. -/
lemma norm_perronAux_horizontal_le {y c T : ℝ} (hy : 0 < y) (hT : T ≠ 0) :
    ‖perronAux y ((c : ℂ) + (T : ℂ) * I)‖ ≤ (y ^ (c + 1) + y + 2) * (T ^ 2)⁻¹ := by
  let s : ℂ := (c : ℂ) + (T : ℂ) * I
  have hs_add1_eq : s + 1 = ((c + 1 : ℝ) : ℂ) + (T : ℂ) * I := by dsimp [s]; push_cast; ring
  have hs_sub1_eq : s - 1 = ((c - 1 : ℝ) : ℂ) + (T : ℂ) * I := by dsimp [s]; push_cast; ring
  have hs0 : s ≠ 0 := ofReal_add_ofReal_mul_I_ne_zero_of_im_ne_zero hT
  have hs_add1 : s + 1 ≠ 0 := by
    rw [hs_add1_eq]; exact ofReal_add_ofReal_mul_I_ne_zero_of_im_ne_zero hT
  have hs_sub1 : s - 1 ≠ 0 := by
    rw [hs_sub1_eq]; exact ofReal_add_ofReal_mul_I_ne_zero_of_im_ne_zero hT
  have h_norm_s : |T| ≤ ‖s‖ := norm_ofReal_add_ofReal_mul_I_ge_abs_im c T
  have h_norm_add1 : |T| ≤ ‖s + 1‖ := by
    rw [hs_add1_eq]; exact norm_ofReal_add_ofReal_mul_I_ge_abs_im (c + 1) T
  have h_norm_sub1 : |T| ≤ ‖s - 1‖ := by
    rw [hs_sub1_eq]; exact norm_ofReal_add_ofReal_mul_I_ge_abs_im (c - 1) T
  have hT2_pos : 0 < T ^ 2 := sq_pos_of_ne_zero hT
  have h_prod1 : T ^ 2 ≤ ‖s‖ * ‖s + 1‖ := by
    rw [← sq_abs T, sq]; exact mul_le_mul h_norm_s h_norm_add1 (abs_nonneg T) (norm_nonneg _)
  have h_prod2 : T ^ 2 ≤ ‖s‖ * ‖s - 1‖ := by
    rw [← sq_abs T, sq]; exact mul_le_mul h_norm_s h_norm_sub1 (abs_nonneg T) (norm_nonneg _)
  have h_prod3 : T ^ 2 ≤ ‖s + 1‖ * ‖s - 1‖ := by
    rw [← sq_abs T, sq]; exact mul_le_mul h_norm_add1 h_norm_sub1 (abs_nonneg T) (norm_nonneg _)
  have h_term1 : ‖smoothedPerronKernel y s‖ ≤ y ^ (c + 1) * (T ^ 2)⁻¹ := by
    dsimp [smoothedPerronKernel]
    rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    have hre : (s + 1).re = c + 1 := by rw [hs_add1_eq]; simp
    rw [hre, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hT2_pos h_prod1) (rpow_nonneg hy.le _)
  have h_term2 : ‖(y : ℂ) / (s * (s - 1))‖ ≤ y * (T ^ 2)⁻¹ := by
    rw [norm_div, norm_mul, Complex.norm_of_nonneg hy.le, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hT2_pos h_prod2) hy.le
  have h_term3 : ‖(2 : ℂ) / ((s + 1) * (s - 1))‖ ≤ 2 * (T ^ 2)⁻¹ := by
    rw [norm_div, norm_mul, Complex.norm_ofNat, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hT2_pos h_prod3) (by positivity)
  change ‖perronAux y s‖ ≤ _
  rw [perronAux_eq_quad_decay hs0 hs_add1 hs_sub1]
  calc ‖smoothedPerronKernel y s + (y : ℂ) / (s * (s - 1)) - 2 / ((s + 1) * (s - 1))‖
      ≤ ‖smoothedPerronKernel y s + (y : ℂ) / (s * (s - 1))‖ +
          ‖(2 : ℂ) / ((s + 1) * (s - 1))‖ := norm_sub_le _ _
    _ ≤ ‖smoothedPerronKernel y s‖ + ‖(y : ℂ) / (s * (s - 1))‖ +
          ‖(2 : ℂ) / ((s + 1) * (s - 1))‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ y ^ (c + 1) * (T ^ 2)⁻¹ + y * (T ^ 2)⁻¹ + 2 * (T ^ 2)⁻¹ :=
          add_le_add (add_le_add h_term1 h_term2) h_term3
    _ = (y ^ (c + 1) + y + 2) * (T ^ 2)⁻¹ := by ring

/-- Vertical line bound for `perronAux y (C + t * I)` when `1 ≤ y` and `C < -1`. -/
lemma norm_perronAux_vertical_le_of_lt_neg_one {y C : ℝ} (hy1 : 1 ≤ y) (hC : C < -1) (t : ℝ) :
    ‖perronAux y ((C : ℂ) + (t : ℂ) * I)‖ ≤ (y + 3) * ((C + 1) ^ 2 + t ^ 2)⁻¹ := by
  have hy : 0 < y := zero_lt_one.trans_le hy1
  let s : ℂ := (C : ℂ) + (t : ℂ) * I
  have hs_add1_eq : s + 1 = ((C + 1 : ℝ) : ℂ) + (t : ℂ) * I := by dsimp [s]; push_cast; ring
  have hs_sub1_eq : s - 1 = ((C - 1 : ℝ) : ℂ) + (t : ℂ) * I := by dsimp [s]; push_cast; ring
  have hs0 : s ≠ 0 := ofReal_add_ofReal_mul_I_ne_zero_of_re_ne_zero (by linarith)
  have hs_add1 : s + 1 ≠ 0 := by
    rw [hs_add1_eq]; exact ofReal_add_ofReal_mul_I_ne_zero_of_re_ne_zero (by linarith)
  have hs_sub1 : s - 1 ≠ 0 := by
    rw [hs_sub1_eq]; exact ofReal_add_ofReal_mul_I_ne_zero_of_re_ne_zero (by linarith)
  have h_sq_pos : 0 < (C + 1) ^ 2 + t ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (by linarith)) (sq_nonneg t)
  have h_norm_add1_sq : ‖s + 1‖ ^ 2 = (C + 1) ^ 2 + t ^ 2 := by
    rw [hs_add1_eq, norm_sq_ofReal_add_ofReal_mul_I]
  have h_le_s : ‖s + 1‖ ≤ ‖s‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), h_norm_add1_sq,
      norm_sq_ofReal_add_ofReal_mul_I]
    nlinarith
  have h_le_sub1 : ‖s + 1‖ ≤ ‖s - 1‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), h_norm_add1_sq, hs_sub1_eq,
      norm_sq_ofReal_add_ofReal_mul_I]
    nlinarith
  have h_prod1 : (C + 1) ^ 2 + t ^ 2 ≤ ‖s‖ * ‖s + 1‖ := by
    rw [← h_norm_add1_sq, sq]
    exact mul_le_mul_of_nonneg_right h_le_s (norm_nonneg _)
  have h_prod2 : (C + 1) ^ 2 + t ^ 2 ≤ ‖s‖ * ‖s - 1‖ := by
    rw [← h_norm_add1_sq, sq]
    exact mul_le_mul h_le_s h_le_sub1 (norm_nonneg _) (norm_nonneg _)
  have h_prod3 : (C + 1) ^ 2 + t ^ 2 ≤ ‖s + 1‖ * ‖s - 1‖ := by
    rw [← h_norm_add1_sq, sq]
    exact mul_le_mul_of_nonneg_left h_le_sub1 (norm_nonneg _)
  have h_yC : y ^ (C + 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy1 (by linarith)
  have h_term1 : ‖smoothedPerronKernel y s‖ ≤ 1 * ((C + 1) ^ 2 + t ^ 2)⁻¹ := by
    dsimp [smoothedPerronKernel]
    rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    have hre : (s + 1).re = C + 1 := by rw [hs_add1_eq]; simp
    rw [hre, div_eq_mul_inv]
    exact mul_le_mul h_yC (inv_anti₀ h_sq_pos h_prod1) (by positivity) zero_le_one
  have h_term2 : ‖(y : ℂ) / (s * (s - 1))‖ ≤ y * ((C + 1) ^ 2 + t ^ 2)⁻¹ := by
    rw [norm_div, norm_mul, Complex.norm_of_nonneg hy.le, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ h_sq_pos h_prod2) hy.le
  have h_term3 : ‖(2 : ℂ) / ((s + 1) * (s - 1))‖ ≤ 2 * ((C + 1) ^ 2 + t ^ 2)⁻¹ := by
    rw [norm_div, norm_mul, Complex.norm_ofNat, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ h_sq_pos h_prod3) (by positivity)
  change ‖perronAux y s‖ ≤ _
  rw [perronAux_eq_quad_decay hs0 hs_add1 hs_sub1]
  calc ‖smoothedPerronKernel y s + (y : ℂ) / (s * (s - 1)) - 2 / ((s + 1) * (s - 1))‖
      ≤ ‖smoothedPerronKernel y s + (y : ℂ) / (s * (s - 1))‖ +
          ‖(2 : ℂ) / ((s + 1) * (s - 1))‖ := norm_sub_le _ _
    _ ≤ ‖smoothedPerronKernel y s‖ + ‖(y : ℂ) / (s * (s - 1))‖ +
          ‖(2 : ℂ) / ((s + 1) * (s - 1))‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ 1 * ((C + 1) ^ 2 + t ^ 2)⁻¹ + y * ((C + 1) ^ 2 + t ^ 2)⁻¹ +
          2 * ((C + 1) ^ 2 + t ^ 2)⁻¹ :=
          add_le_add (add_le_add h_term1 h_term2) h_term3
    _ = (y + 3) * ((C + 1) ^ 2 + t ^ 2)⁻¹ := by ring

/-- Integrability of `t ↦ perronAux y (C + t * I)` for `1 ≤ y` and `C < -1`. -/
lemma integrable_perronAux_of_lt_neg_one {y C : ℝ} (hy1 : 1 ≤ y) (hC : C < -1) :
    Integrable (fun t : ℝ ↦ perronAux y ((C : ℂ) + (t : ℂ) * I)) := by
  have hy : 0 < y := zero_lt_one.trans_le hy1
  have hC1 : C + 1 ≠ 0 := by linarith
  refine ((integrable_inv_sq_add_sq hC1).const_mul (y + 3)).mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    have h_cont : Continuous (fun t : ℝ ↦ (C : ℂ) + (t : ℂ) * I) := by fun_prop
    refine (differentiableOn_perronAux hy).continuousOn.comp_continuous h_cont fun t ↦ ?_
    change ((C : ℂ) + (t : ℂ) * I).re < 1
    rw [re_ofReal_add_ofReal_mul_I]
    linarith
  · filter_upwards with t
    exact norm_perronAux_vertical_le_of_lt_neg_one hy1 hC t

/-- For `0 < y` and `c ∈ (0, 1)`, `t ↦ perronAux y (c + t * I)` is integrable and its integral is
`(∫ t, smoothedPerronKernel y (c + t * I)) - 2 * π * (y - 1)`. -/
lemma integrable_and_integral_perronAux_of_mem_Ioo {y c : ℝ} (hy : 0 < y) (hc0 : 0 < c)
    (hc1 : c < 1) :
    Integrable (fun t : ℝ ↦ perronAux y ((c : ℂ) + (t : ℂ) * I)) ∧
      (∫ t : ℝ, perronAux y ((c : ℂ) + (t : ℂ) * I)) =
        (∫ t : ℝ, smoothedPerronKernel y ((c : ℂ) + (t : ℂ) * I)) -
          2 * π * ((y : ℂ) - 1) := by
  have h_eq : (fun t : ℝ ↦ perronAux y ((c : ℂ) + (t : ℂ) * I)) =
      fun t : ℝ ↦ smoothedPerronKernel y ((c : ℂ) + (t : ℂ) * I) -
        (y : ℂ) * (((c : ℂ) + (t : ℂ) * I)⁻¹ - (((c - 1 : ℝ) : ℂ) + (t : ℂ) * I)⁻¹) +
        ((((c + 1 : ℝ) : ℂ) + (t : ℂ) * I)⁻¹ - (((c - 1 : ℝ) : ℂ) + (t : ℂ) * I)⁻¹) := by
    ext t
    have hs0 : (c : ℂ) + (t : ℂ) * I ≠ 0 := ofReal_add_ofReal_mul_I_ne_zero_of_re_ne_zero hc0.ne'
    have h_add1 : (c : ℂ) + (t : ℂ) * I + 1 = ((c + 1 : ℝ) : ℂ) + (t : ℂ) * I := by
      push_cast; ring
    have h_sub1 : (c : ℂ) + (t : ℂ) * I - 1 = ((c - 1 : ℝ) : ℂ) + (t : ℂ) * I := by
      push_cast; ring
    have hs_add1 : (c : ℂ) + (t : ℂ) * I + 1 ≠ 0 := by
      rw [h_add1]; exact ofReal_add_ofReal_mul_I_ne_zero_of_re_ne_zero (by linarith)
    rw [perronAux_eq_pole_sub hs0 hs_add1, h_add1, h_sub1]
  have h_int1 : Integrable (fun t : ℝ ↦ smoothedPerronKernel y ((c : ℂ) + (t : ℂ) * I)) :=
    integrable_smoothedPerronKernel hy hc0
  have h_int2 : Integrable (fun t : ℝ ↦
      ((c : ℂ) + (t : ℂ) * I)⁻¹ - (((c - 1 : ℝ) : ℂ) + (t : ℂ) * I)⁻¹) :=
    integrable_inv_sub_inv_ofReal_add_ofReal_mul_I hc0.ne' (by linarith)
  have h_int2_y : Integrable (fun t : ℝ ↦
      (y : ℂ) * (((c : ℂ) + (t : ℂ) * I)⁻¹ - (((c - 1 : ℝ) : ℂ) + (t : ℂ) * I)⁻¹)) :=
    h_int2.const_mul (y : ℂ)
  have h_int12 : Integrable (fun t : ℝ ↦
      smoothedPerronKernel y ((c : ℂ) + (t : ℂ) * I) -
        (y : ℂ) * (((c : ℂ) + (t : ℂ) * I)⁻¹ - (((c - 1 : ℝ) : ℂ) + (t : ℂ) * I)⁻¹)) :=
    Integrable.sub h_int1 h_int2_y
  have h_int3 : Integrable (fun t : ℝ ↦
      (((c + 1 : ℝ) : ℂ) + (t : ℂ) * I)⁻¹ - (((c - 1 : ℝ) : ℂ) + (t : ℂ) * I)⁻¹) :=
    integrable_inv_sub_inv_ofReal_add_ofReal_mul_I (by linarith) (by linarith)
  refine ⟨?_, ?_⟩
  · rw [h_eq]
    exact Integrable.add h_int12 h_int3
  · rw [h_eq, integral_add h_int12 h_int3, integral_sub h_int1 h_int2_y, integral_const_mul,
      integral_inv_sub_inv_ofReal_add_ofReal_mul_I hc0 (by linarith),
      integral_inv_sub_inv_ofReal_add_ofReal_mul_I (by linarith) (by linarith)]
    ring

end ConjectureMachines.Semantics.Riemann.WeightedStieltjes
