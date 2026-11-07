/- GID: D5/S3/Weil/Mertens/Cryptids/Schmidt
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/Cryptids/Schmidt
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original Cryptids Schmidt analytic source for the RH Chebyshev bound. -/

/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in
  docs/reports/licenses/cryptids-LICENSE.txt.
Source: https://github.com/google-deepmind/cryptids/blob/e5f59ed70d1549a61ef8873a6fbae9268fdbd557/Cryptids/Semantics/Riemann/Schmidt.lean
Routing adaptations: ordinary D5 modules, redirected imports, and declaration-boundary splitting.
The original declaration namespaces, statements, and mathematical proof text are retained.
Retirement: when this repository's lake-manifest.json Mathlib revision provides an equivalent
RH-only real-x Chebyshev psi estimate for x >= 5000, replace the target with that declaration
and delete the transplanted declarations no longer in its live dependency closure.
-/

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Positivity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.Positivity
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.ZetaZeros

/-! Original Schmidt analytic supplier for the RH Chebyshev estimate. -/

namespace RiemannSchmidt


open Complex Finset Filter MeasureTheory Asymptotics Set Topology
open scoped Real Topology Nat ENNReal LSeries.notation ArithmeticFunction

/-- The fractional-part kernel on `(1, ∞)`:
`fractKernel t = t - ⌊t⌋₊` for `t > 1`, and `0` for `t ≤ 1`. -/
noncomputable def fractKernel : ℝ → ℂ :=
  (Ioi (1 : ℝ)).indicator (fun t : ℝ ↦ ((t - ⌊t⌋₊ : ℝ) : ℂ))

/-- For `t ≥ 0`, `0 ≤ t - ⌊t⌋₊` and `t - ⌊t⌋₊ ≤ 1`. -/
theorem sub_floor_bounds {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ t - (⌊t⌋₊ : ℝ) ∧ t - (⌊t⌋₊ : ℝ) ≤ 1 := by
  refine ⟨sub_nonneg.mpr (Nat.floor_le ht), ?_⟩
  linarith [Nat.lt_floor_add_one t]

/-- `‖fractKernel t‖ ≤ 1` for all `t : ℝ`. -/
theorem norm_fractKernel_le_one (t : ℝ) : ‖fractKernel t‖ ≤ 1 := by
  unfold fractKernel
  by_cases ht : t ∈ Ioi (1 : ℝ)
  · rw [indicator_of_mem ht, norm_real, Real.norm_eq_abs]
    have ht0 : 0 ≤ t := by linarith [mem_Ioi.mp ht]
    obtain ⟨h0, h1⟩ := sub_floor_bounds ht0
    rw [abs_of_nonneg h0]
    exact h1
  · rw [indicator_of_notMem ht, norm_zero]
    exact zero_le_one

/-- `fractKernel` is measurable. -/
theorem measurable_fractKernel : Measurable fractKernel := by
  unfold fractKernel
  refine Measurable.indicator ?_ measurableSet_Ioi
  exact Complex.measurable_ofReal.comp
    (measurable_id.sub (measurable_from_nat.comp Nat.measurable_floor))

/-- `fractKernel` is locally integrable on `Ioi 0`. -/
theorem locallyIntegrableOn_fractKernel : LocallyIntegrableOn fractKernel (Ioi 0) := by
  intro x _
  refine ⟨Metric.closedBall x 1, nhdsWithin_le_nhds (Metric.closedBall_mem_nhds x zero_lt_one), ?_⟩
  refine (integrableOn_const (C := (1 : ℝ))
    (hs := (isCompact_closedBall x 1).measure_lt_top.ne)).mono'
    measurable_fractKernel.aestronglyMeasurable ?_
  exact Eventually.of_forall norm_fractKernel_le_one

/-- `fractKernel` is `O(t ^ (-(0 : ℝ)))` as `t → ∞`. -/
theorem isBigO_fractKernel_atTop :
    fractKernel =O[atTop] (fun t : ℝ ↦ t ^ (-(0 : ℝ))) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t _
  simp [norm_fractKernel_le_one t]

/-- `fractKernel` vanishes on `Ioo 0 1`, so it is `O(t ^ (-b))` at `𝓝[>] 0` for every `b : ℝ`. -/
theorem isBigO_fractKernel_nhdsGT_zero (b : ℝ) :
    fractKernel =O[𝓝[>] 0] (fun t : ℝ ↦ t ^ (-b)) := by
  refine IsBigO.of_bound 0 ?_
  have hmem : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT zero_lt_one
  filter_upwards [hmem] with t ht
  have hnot : t ∉ Ioi (1 : ℝ) := notMem_Ioi.mpr ht.2.le
  simp [fractKernel, indicator_of_notMem hnot]

/-- For every `z : ℂ` with `z.re < 0`, `MellinConvergent fractKernel z` holds. -/
theorem mellinConvergent_fractKernel {z : ℂ} (hz : z.re < 0) :
    MellinConvergent fractKernel z :=
  mellinConvergent_of_isBigO_rpow locallyIntegrableOn_fractKernel
    isBigO_fractKernel_atTop hz (isBigO_fractKernel_nhdsGT_zero (z.re - 1)) (by linarith)

/-- For every `z : ℂ` with `z.re < 0`, `mellin fractKernel` is complex-differentiable at `z`. -/
theorem differentiableAt_mellin_fractKernel {z : ℂ} (hz : z.re < 0) :
    DifferentiableAt ℂ (mellin fractKernel) z :=
  mellin_differentiableAt_of_isBigO_rpow locallyIntegrableOn_fractKernel
    isBigO_fractKernel_atTop hz (isBigO_fractKernel_nhdsGT_zero (z.re - 1)) (by linarith)

/-- For every `s : ℂ` with `0 < s.re`, `s ↦ s * mellin fractKernel (-s)` is differentiable
at `s`. -/
theorem differentiableAt_mul_mellin_fractKernel_neg {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ ↦ z * mellin fractKernel (-z)) s := by
  refine DifferentiableAt.mul differentiableAt_id ?_
  exact (differentiableAt_mellin_fractKernel (by simpa using hs)).comp s differentiableAt_id.neg

/-- Rewriting `mellin fractKernel (-s)` as an integral over `Ioi 1`. -/
theorem mellin_fractKernel_neg_eq (s : ℂ) :
    mellin fractKernel (-s) =
      ∫ t in Ioi (1 : ℝ), ((t - ⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  unfold mellin fractKernel
  simp_rw [← indicator_smul, setIntegral_indicator measurableSet_Ioi,
    Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi zero_le_one)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  rw [smul_eq_mul, mul_comm, show -s - 1 = -(s + 1) by ring]

/-- For `1 < s.re`, `riemannZeta s = s * ∫ t in Ioi 1, ⌊t⌋₊ * t ^ (-(s + 1))`. -/
theorem riemannZeta_eq_mul_integral_floor {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s =
      s * ∫ t in Ioi (1 : ℝ), (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  rw [← LSeries_one_eq_riemannZeta hs]
  have hO : (fun n : ℕ ↦ ∑ _k ∈ Finset.Icc 1 n, (1 : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 0] with n _
    simp
  have h := LSeries_eq_mul_integral_of_nonneg (fun _ : ℕ ↦ (1 : ℝ)) zero_le_one hs hO
    (fun _ ↦ zero_le_one)
  have hL : LSeries (fun _ : ℕ ↦ ((1 : ℝ) : ℂ)) s = LSeries 1 s := by simp; rfl
  rw [← hL, h]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  simp

/-- For `1 < s.re`, `∫ t in Ioi 1, t * t ^ (-(s + 1)) = (s - 1)⁻¹`. -/
theorem integral_Ioi_one_mul_cpow_neg_add_one {s : ℂ} (hs : 1 < s.re) :
    ∫ t in Ioi (1 : ℝ), (t : ℂ) * (t : ℂ) ^ (-(s + 1)) = (s - 1)⁻¹ := by
  have hcongr : EqOn (fun t : ℝ ↦ (t : ℂ) * (t : ℂ) ^ (-(s + 1)))
      (fun t : ℝ ↦ (t : ℂ) ^ (-s)) (Ioi (1 : ℝ)) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (zero_lt_one.trans ht).ne'
    calc
      (t : ℂ) * (t : ℂ) ^ (-(s + 1))
        = (t : ℂ) ^ (1 : ℂ) * (t : ℂ) ^ (-(s + 1)) := by rw [cpow_one]
      _ = (t : ℂ) ^ (1 + -(s + 1)) := (cpow_add _ _ ht0).symm
      _ = (t : ℂ) ^ (-s) := by ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr]
  have ha : (-s).re < -1 := by simpa using hs
  rw [integral_Ioi_cpow_of_lt ha zero_lt_one]
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (by intro h; subst h; simp at hs)
  have h1 : -s + 1 = -(s - 1) := by ring
  rw [ofReal_one, one_cpow, h1, div_neg, neg_div, neg_neg, one_div]

/-- For `1 < s.re`, `1 - riemannZeta₀ s = s * mellin fractKernel (-s)`. -/
theorem one_sub_riemannZeta₀_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    1 - riemannZeta₀ s = s * mellin fractKernel (-s) := by
  have hs1 : s ≠ 1 := by intro h; subst h; simp at hs
  have hs1_sub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hzeta := riemannZeta_eq_inv_sub_add hs1
  have hfloor := riemannZeta_eq_mul_integral_floor hs
  have hint_t := integral_Ioi_one_mul_cpow_neg_add_one hs
  have ha : (-s).re < -1 := by simpa using hs
  have hint1 : IntegrableOn (fun t : ℝ ↦ (t : ℂ) * (t : ℂ) ^ (-(s + 1))) (Ioi (1 : ℝ)) := by
    refine (integrableOn_Ioi_cpow_of_lt ha zero_lt_one).congr_fun ?_ measurableSet_Ioi
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (zero_lt_one.trans ht).ne'
    calc
      (t : ℂ) ^ (-s) = (t : ℂ) ^ (1 + -(s + 1)) := by ring_nf
      _ = (t : ℂ) ^ (1 : ℂ) * (t : ℂ) ^ (-(s + 1)) := cpow_add _ _ ht0
      _ = (t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by rw [cpow_one]
  have hint_fract : IntegrableOn
      (fun t : ℝ ↦ ((t - ⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Ioi (1 : ℝ)) := by
    have hm := mellinConvergent_fractKernel (z := -s) (by simpa using zero_lt_one.trans hs)
    unfold MellinConvergent fractKernel at hm
    rw [IntegrableOn, ← indicator_smul, integrable_indicator_iff measurableSet_Ioi,
      IntegrableOn, Measure.restrict_restrict_of_subset (Set.Ioi_subset_Ioi zero_le_one)] at hm
    change IntegrableOn _ (Ioi (1 : ℝ)) volume at hm
    refine hm.congr_fun ?_ measurableSet_Ioi
    intro t _
    dsimp only
    rw [smul_eq_mul, mul_comm, show -s - 1 = -(s + 1) by ring]
  have hint_floor : IntegrableOn
      (fun t : ℝ ↦ (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) (Ioi (1 : ℝ)) := by
    refine (hint1.sub hint_fract).congr_fun ?_ measurableSet_Ioi
    intro t _
    rw [Pi.sub_apply]
    push_cast
    ring
  rw [mellin_fractKernel_neg_eq]
  have hsub : ∫ t in Ioi (1 : ℝ), ((t - ⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      (∫ t in Ioi (1 : ℝ), (t : ℂ) * (t : ℂ) ^ (-(s + 1))) -
        ∫ t in Ioi (1 : ℝ), (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
    rw [← integral_sub hint1 hint_floor]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
    push_cast
    ring
  rw [hsub, mul_sub, hint_t, ← hfloor, hzeta]
  have h1 : s * (s - 1)⁻¹ - (s - 1)⁻¹ = 1 := by
    calc
      s * (s - 1)⁻¹ - (s - 1)⁻¹ = (s - 1) * (s - 1)⁻¹ := by ring
      _ = 1 := mul_inv_cancel₀ hs1_sub
  linear_combination -h1

/-- Open right half-planes `{z : ℂ | σ₀ < z.re}` are convex. -/
theorem convex_halfPlane_re_gt (σ₀ : ℝ) : Convex ℝ {z : ℂ | σ₀ < z.re} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq, add_re, smul_re, smul_eq_mul] at hx hy ⊢
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · simp only [zero_mul, zero_add] at hab ⊢
    subst hab
    simpa using hy
  · have : a * σ₀ < a * x.re := mul_lt_mul_of_pos_left hx ha_pos
    have : b * σ₀ ≤ b * y.re := mul_le_mul_of_nonneg_left hy.le hb
    calc
      σ₀ = (a + b) * σ₀ := by rw [hab, one_mul]
      _ = a * σ₀ + b * σ₀ := add_mul a b σ₀
      _ < a * x.re + b * y.re := by linarith

/-- For every `s : ℂ` with `0 < s.re`, `1 - riemannZeta₀ s = s * mellin fractKernel (-s)`. -/
theorem one_sub_riemannZeta₀_eq_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    1 - riemannZeta₀ s = s * mellin fractKernel (-s) := by
  have hOpen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hPre : IsPreconnected {z : ℂ | 0 < z.re} := (convex_halfPlane_re_gt 0).isPreconnected
  have hAn1 : AnalyticOnNhd ℂ (fun z : ℂ ↦ 1 - riemannZeta₀ z) {z : ℂ | 0 < z.re} := by
    refine DifferentiableOn.analyticOnNhd ?_ hOpen
    exact (differentiable_const (1 : ℂ)).sub differentiable_riemannZeta₀ |>.differentiableOn
  have hAn2 : AnalyticOnNhd ℂ (fun z : ℂ ↦ z * mellin fractKernel (-z)) {z : ℂ | 0 < z.re} := by
    refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) hOpen
    exact (differentiableAt_mul_mellin_fractKernel_neg hz).differentiableWithinAt
  have hEv : (fun z : ℂ ↦ 1 - riemannZeta₀ z) =ᶠ[𝓝 (2 : ℂ)]
      (fun z : ℂ ↦ z * mellin fractKernel (-z)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    exact one_sub_riemannZeta₀_eq_of_one_lt_re hz
  exact hAn1.eqOn_of_preconnected_of_eventuallyEq hAn2 hPre (by norm_num : (2 : ℂ) ∈ _) hEv hs

/-- The Riemann zeta function does not have infinite analytic order at any point `ρ ≠ 1`. -/
theorem analyticOrderAt_riemannZeta_ne_top {ρ : ℂ} (hρ1 : ρ ≠ 1) :
    analyticOrderAt riemannZeta ρ ≠ ⊤ := by
  have hconn : IsConnected ({(1 : ℂ)}ᶜ : Set ℂ) :=
    isConnected_compl_singleton_of_one_lt_rank (by simp) 1
  have h2 : (2 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by simp
  have h2_ne_top : analyticOrderAt riemannZeta 2 ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr
      (Or.inr (riemannZeta_ne_zero_of_one_le_re (by norm_num : (1 : ℝ) ≤ (2 : ℂ).re)))]
    exact ENat.zero_ne_top
  exact analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected
    hconn.isPreconnected h2 hρ1 h2_ne_top

end RiemannSchmidt
