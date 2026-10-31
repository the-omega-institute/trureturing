/- GID: D5/S3/Weil/Mertens/Cryptids/VonMangoldtCount/Foundation
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/Cryptids/VonMangoldtCount/Foundation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original Cryptids VonMangoldtCount analytic source for the RH Chebyshev bound. -/

/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in
  docs/reports/licenses/cryptids-LICENSE.txt.
Source: https://github.com/google-deepmind/cryptids/blob/e5f59ed70d1549a61ef8873a6fbae9268fdbd557/Cryptids/Semantics/Riemann/VonMangoldtCount.lean
Routing adaptations: ordinary D5 modules, redirected imports, and declaration-boundary splitting.
The original declaration namespaces, statements, and mathematical proof text are retained.
Retirement: when this repository's lake-manifest.json Mathlib revision provides an equivalent
RH-only real-x Chebyshev psi estimate for x >= 5000, replace the target with that declaration
and delete the transplanted declarations no longer in its live dependency closure.
-/

import D5.S3.Weil.Mertens.Cryptids.Schmidt
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.ZetaZeros

/-! Original VonMangoldtCount analytic supplier for the RH Chebyshev estimate. -/

namespace ConjectureMachines.Semantics.Riemann.VonMangoldtCount

export RiemannSchmidt
  (sub_floor_bounds)

open Complex Finset Filter MeasureTheory Set Asymptotics Metric MeromorphicOn
open scoped Real Topology ArithmeticFunction LSeries.notation

/-- For `t ≥ 0`, `0 ≤ (t - ⌊t⌋₊) ^ 2 * (1 - (t - ⌊t⌋₊)) ^ 2 ≤ 1 / 16`. -/
theorem quartic_floor_bounds {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ (t - (⌊t⌋₊ : ℝ)) ^ 2 * (1 - (t - (⌊t⌋₊ : ℝ))) ^ 2 ∧
      (t - (⌊t⌋₊ : ℝ)) ^ 2 * (1 - (t - (⌊t⌋₊ : ℝ))) ^ 2 ≤ 1 / 16 := by
  obtain ⟨h0, h1⟩ := sub_floor_bounds ht
  refine ⟨by positivity, ?_⟩
  set u := t - (⌊t⌋₊ : ℝ)
  have hu_nonneg : 0 ≤ u * (1 - u) := mul_nonneg h0 (sub_nonneg.mpr h1)
  have hu_le : u * (1 - u) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (u - 1 / 2)]
  calc
    u ^ 2 * (1 - u) ^ 2 = (u * (1 - u)) * (u * (1 - u)) := by ring
    _ ≤ (1 / 4) * (1 / 4) := mul_le_mul hu_le hu_le hu_nonneg (by positivity)
    _ = 1 / 16 := by norm_num

/-- The fourth-order Euler–Maclaurin kernel on `(1, ∞)`:
`quarticKernel t = (t - ⌊t⌋₊) ^ 2 * (1 - (t - ⌊t⌋₊)) ^ 2` for `t > 1`, and `0` for `t ≤ 1`. -/
noncomputable def quarticKernel : ℝ → ℂ :=
  (Ioi (1 : ℝ)).indicator
    (fun t : ℝ ↦ (((t - ⌊t⌋₊) ^ 2 * (1 - (t - ⌊t⌋₊)) ^ 2 : ℝ) : ℂ))

/-- `‖quarticKernel t‖ ≤ 1 / 16` for all `t : ℝ`. -/
theorem norm_quarticKernel_le_one_sixteenth (t : ℝ) : ‖quarticKernel t‖ ≤ 1 / 16 := by
  unfold quarticKernel
  by_cases ht : t ∈ Ioi (1 : ℝ)
  · rw [indicator_of_mem ht, norm_real, Real.norm_eq_abs]
    have ht0 : 0 ≤ t := by linarith [mem_Ioi.mp ht]
    obtain ⟨h0, h1⟩ := quartic_floor_bounds ht0
    rw [abs_of_nonneg h0]
    exact h1
  · rw [indicator_of_notMem ht, norm_zero]
    norm_num

/-- `quarticKernel` is measurable. -/
theorem measurable_quarticKernel : Measurable quarticKernel := by
  unfold quarticKernel
  refine Measurable.indicator ?_ measurableSet_Ioi
  have hm : Measurable (fun t : ℝ ↦ t - (⌊t⌋₊ : ℝ)) :=
    measurable_id.sub (measurable_from_nat.comp Nat.measurable_floor)
  exact Complex.measurable_ofReal.comp
    ((hm.pow_const 2).mul ((measurable_const.sub hm).pow_const 2))

/-- `quarticKernel` is locally integrable on `Ioi 0`. -/
theorem locallyIntegrableOn_quarticKernel : LocallyIntegrableOn quarticKernel (Ioi 0) := by
  intro x _
  refine ⟨Metric.closedBall x 1, nhdsWithin_le_nhds (Metric.closedBall_mem_nhds x zero_lt_one), ?_⟩
  refine (integrableOn_const (C := (1 / 16 : ℝ))
    (hs := (isCompact_closedBall x 1).measure_lt_top.ne)).mono'
    measurable_quarticKernel.aestronglyMeasurable ?_
  exact Eventually.of_forall norm_quarticKernel_le_one_sixteenth

/-- `quarticKernel` is `O(t ^ (-(0 : ℝ)))` as `t → ∞`. -/
theorem isBigO_quarticKernel_atTop :
    quarticKernel =O[atTop] (fun t : ℝ ↦ t ^ (-(0 : ℝ))) := by
  refine IsBigO.of_bound (1 / 16) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t _
  simpa using norm_quarticKernel_le_one_sixteenth t

/-- `quarticKernel` vanishes on `Ioo 0 1`, so it is `O(t ^ (-b))` at `𝓝[>] 0` for every `b : ℝ`. -/
theorem isBigO_quarticKernel_nhdsGT_zero (b : ℝ) :
    quarticKernel =O[𝓝[>] 0] (fun t : ℝ ↦ t ^ (-b)) := by
  refine IsBigO.of_bound 0 ?_
  have hmem : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT zero_lt_one
  filter_upwards [hmem] with t ht
  have hnot : t ∉ Ioi (1 : ℝ) := notMem_Ioi.mpr ht.2.le
  simp [quarticKernel, indicator_of_notMem hnot]

/-- For every `z : ℂ` with `z.re < 0`, `mellin quarticKernel` is complex-differentiable at `z`. -/
theorem differentiableAt_mellin_quarticKernel {z : ℂ} (hz : z.re < 0) :
    DifferentiableAt ℂ (mellin quarticKernel) z :=
  mellin_differentiableAt_of_isBigO_rpow locallyIntegrableOn_quarticKernel
    isBigO_quarticKernel_atTop hz (isBigO_quarticKernel_nhdsGT_zero (z.re - 1)) (by linarith)

/-- Rewriting `mellin quarticKernel (-(s + 3))` as an integral over `Ioi 1`. -/
theorem mellin_quarticKernel_neg_add_three_eq (s : ℂ) :
    mellin quarticKernel (-(s + 3)) =
      ∫ t in Ioi (1 : ℝ),
        (((t - ⌊t⌋₊) ^ 2 * (1 - (t - ⌊t⌋₊)) ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 4)) := by
  unfold mellin quarticKernel
  simp_rw [← indicator_smul]
  rw [setIntegral_indicator measurableSet_Ioi,
    Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi zero_le_one)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  rw [smul_eq_mul, mul_comm, show -(s + 3) - 1 = -(s + 4) by ring]

/-- General bound on power sums: for `0 ≤ a` and `m, n : ℕ`,
`0 ≤ ∑ k ∈ Icc 1 n, a * (k : ℝ) ^ m` and
`∑ k ∈ Icc 1 n, a * (k : ℝ) ^ m ≤ a * (n : ℝ) ^ (m + 1 : ℝ)`. -/
theorem sum_Icc_const_mul_pow_bounds {a : ℝ} (ha : 0 ≤ a) (m n : ℕ) :
    0 ≤ ∑ k ∈ Finset.Icc 1 n, a * (k : ℝ) ^ m ∧
      ∑ k ∈ Finset.Icc 1 n, a * (k : ℝ) ^ m ≤ a * (n : ℝ) ^ (m + 1 : ℝ) := by
  refine ⟨Finset.sum_nonneg fun k _ ↦ by positivity, ?_⟩
  have hle : ∑ k ∈ Finset.Icc 1 n, a * (k : ℝ) ^ m ≤
      ∑ _k ∈ Finset.Icc 1 n, a * (n : ℝ) ^ m := by
    refine Finset.sum_le_sum fun k hk ↦ ?_
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hk).2
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg k) hkn m) ha
  rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at hle
  have hrpow : (n : ℝ) * (a * (n : ℝ) ^ m) = a * (n : ℝ) ^ (m + 1 : ℝ) := by
    have h1 : (n : ℝ) ^ (m + 1 : ℝ) = (n : ℝ) ^ (m + 1 : ℕ) := by norm_cast
    rw [h1, pow_succ]
    ring
  linarith

/-- Shifting `LSeries` by `m : ℕ` for `a * k ^ m` yields `a * riemannZeta s` when `1 < s.re`. -/
theorem LSeries_const_mul_pow_add_nat_eq {s : ℂ} (hs : 1 < s.re) (a : ℝ) (m : ℕ) :
    LSeries (fun k : ℕ ↦ ((a * (k : ℝ) ^ m : ℝ) : ℂ)) (s + m) = (a : ℂ) * riemannZeta s := by
  rw [← LSeries_one_eq_riemannZeta hs, LSeries, LSeries, ← tsum_mul_left]
  refine tsum_congr fun k ↦ ?_
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · rw [LSeries.term_of_ne_zero hk, LSeries.term_of_ne_zero hk, Pi.one_apply]
    have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
    rw [cpow_add _ _ hk0, cpow_natCast]
    have hpow0 : (k : ℂ) ^ m ≠ 0 := pow_ne_zero m hk0
    push_cast
    field_simp [hpow0]

/-- General `IntegrableOn` for floor power-sum polynomials `(P ⌊t⌋₊ : ℂ) * t ^ (-(s + m + 1))`
on `Ioi 1` when `1 < s.re`. -/
theorem integrableOn_floor_poly_mul_cpow {s : ℂ} (hs : 1 < s.re) {a : ℝ} (ha : 0 ≤ a)
    (m : ℕ) {P : ℕ → ℝ} (hP : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, a * (k : ℝ) ^ m = P n) :
    IntegrableOn (fun t : ℝ ↦ (P ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + m + 1))) (Ioi (1 : ℝ)) := by
  have hrpow : IntegrableOn (fun t : ℝ ↦ a * t ^ (-s.re)) (Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul a
  refine hrpow.mono' ?_ ?_
  · refine AEStronglyMeasurable.mul ?_ ?_
    · exact (Complex.measurable_ofReal.comp
        (measurable_from_nat.comp Nat.measurable_floor)).aestronglyMeasurable
    · refine (continuousOn_of_forall_continuousAt fun t ht ↦ ?_).aestronglyMeasurable
        measurableSet_Ioi
      exact continuousAt_ofReal_cpow_const _ _ (Or.inr (zero_lt_one.trans ht).ne')
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht_pos : 0 < t := zero_lt_one.trans ht
    obtain ⟨h0, h1⟩ := sum_Icc_const_mul_pow_bounds ha m ⌊t⌋₊
    rw [hP ⌊t⌋₊] at h0 h1
    rw [norm_mul, norm_real, Real.norm_of_nonneg h0, norm_cpow_eq_rpow_re_of_pos ht_pos]
    have hre : (-(s + (m : ℂ) + 1)).re = -s.re - (m + 1 : ℝ) := by simp; ring
    rw [hre]
    have hfloor_le : (⌊t⌋₊ : ℝ) ^ (m + 1 : ℝ) ≤ t ^ (m + 1 : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le ht_pos.le) (by positivity)
    calc
      P ⌊t⌋₊ * t ^ (-s.re - (m + 1 : ℝ))
        ≤ a * (⌊t⌋₊ : ℝ) ^ (m + 1 : ℝ) * t ^ (-s.re - (m + 1 : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht_pos.le _)
      _ ≤ a * t ^ (m + 1 : ℝ) * t ^ (-s.re - (m + 1 : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfloor_le ha)
            (Real.rpow_nonneg ht_pos.le _)
      _ = a * (t ^ (m + 1 : ℝ) * t ^ (-s.re - (m + 1 : ℝ))) := by ring
      _ = a * t ^ (-s.re) := by
          rw [← Real.rpow_add ht_pos]
          ring_nf

/-- General Mellin–Dirichlet evaluation for floor power-sum polynomials:
for `1 < s.re`, `∫ t in Ioi 1, (P ⌊t⌋₊ : ℂ) * t ^ (-(s + m + 1)) = a * riemannZeta s / (s + m)`. -/
theorem integral_floor_poly_mul_cpow_eq {s : ℂ} (hs : 1 < s.re) {a : ℝ} (ha : 0 ≤ a)
    (m : ℕ) {P : ℕ → ℝ} (hP : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, a * (k : ℝ) ^ m = P n) :
    ∫ t in Ioi (1 : ℝ), (P ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + m + 1)) =
      (a : ℂ) * riemannZeta s / (s + m) := by
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, a * (k : ℝ) ^ m) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (m + 1 : ℝ) := by
    refine IsBigO.of_bound a ?_
    filter_upwards [eventually_ge_atTop 0] with n _
    obtain ⟨h0, h1⟩ := sum_Icc_const_mul_pow_bounds ha m n
    rw [Real.norm_of_nonneg h0,
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    exact h1
  have hs_add : (m + 1 : ℝ) < (s + m).re := by simp; linarith
  have h := LSeries_eq_mul_integral_of_nonneg (fun k : ℕ ↦ a * (k : ℝ) ^ m)
    (by positivity : (0 : ℝ) ≤ m + 1) hs_add hO (fun k ↦ by positivity)
  rw [LSeries_const_mul_pow_add_nat_eq hs a m] at h
  have hsm_ne : s + (m : ℂ) ≠ 0 := by
    intro h0
    have hre := congrArg Complex.re h0
    simp at hre
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have h_int_congr :
      (∫ t in Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (a * (k : ℝ) ^ m : ℝ) : ℂ) *
        (t : ℂ) ^ (-(s + (m : ℂ) + 1))) =
      ∫ t in Ioi (1 : ℝ), (P ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + (m : ℂ) + 1)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
    rw [← ofReal_sum, hP ⌊t⌋₊]
  rw [← h_int_congr, h, mul_div_cancel_left₀ _ hsm_ne]

theorem sum_Icc_pow_zero (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) * (k : ℝ) ^ 0 = (n : ℝ) := by
  simp

theorem sum_Icc_two_mul_pow_one (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (2 : ℝ) * (k : ℝ) ^ 1 = (n : ℝ) * ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
    push_cast
    ring

theorem sum_Icc_six_mul_pow_two (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (6 : ℝ) * (k : ℝ) ^ 2 =
      (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
    push_cast
    ring

theorem sum_Icc_four_mul_pow_three (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (4 : ℝ) * (k : ℝ) ^ 3 =
      (n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
    push_cast
    ring

/-- For `0 < z.re`, `∫ t in Ioi 1, (t : ℂ) ^ (-(z + 1)) = 1 / z`. -/
theorem integral_Ioi_one_cpow_neg_add_one {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-(z + 1)) = 1 / z := by
  have hlt : (-(z + 1)).re < -1 := by simp only [neg_re, add_re, one_re]; linarith
  rw [integral_Ioi_cpow_of_lt hlt zero_lt_one]
  have h1 : -(z + 1) + 1 = -z := by ring
  rw [ofReal_one, one_cpow, h1, div_neg, neg_div, neg_neg]

/-- **Fourth-Order Euler–Maclaurin Identity for `mellin quarticKernel (-(s + 3))` on `1 < s.re`**:
For every `s : ℂ` with `1 < s.re`,
$$\operatorname{mellin}\;\text{quarticKernel}\;(-(s + 3))
  = \frac{2}{(s - 1) s (s + 1)} - \frac{24}{s (s + 1) (s + 2) (s + 3)} \zeta(s).$$ -/
theorem mellin_quarticKernel_neg_add_three_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    mellin quarticKernel (-(s + 3)) =
      2 / ((s - 1) * s * (s + 1)) -
        24 / (s * (s + 1) * (s + 2) * (s + 3)) * riemannZeta s := by
  let g0 : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (-s)
  let g1 : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (-(s + 1))
  let g2 : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (-(s + 2))
  let p0 : ℝ → ℂ := fun t ↦ ((⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ) ^ (-(s + (0 : ℕ) + 1))
  let p1 : ℝ → ℂ := fun t ↦ (((⌊t⌋₊ : ℝ) * ((⌊t⌋₊ : ℝ) + 1) : ℝ) : ℂ) *
    (t : ℂ) ^ (-(s + (1 : ℕ) + 1))
  let p2 : ℝ → ℂ := fun t ↦ (((⌊t⌋₊ : ℝ) * ((⌊t⌋₊ : ℝ) + 1) * (2 * (⌊t⌋₊ : ℝ) + 1) : ℝ) : ℂ) *
    (t : ℂ) ^ (-(s + (2 : ℕ) + 1))
  let p3 : ℝ → ℂ := fun t ↦ (((⌊t⌋₊ : ℝ) ^ 2 * ((⌊t⌋₊ : ℝ) + 1) ^ 2 : ℝ) : ℂ) *
    (t : ℂ) ^ (-(s + (3 : ℕ) + 1))
  have hint_g0 : IntegrableOn g0 (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one
  have hint_g1 : IntegrableOn g1 (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one
  have hint_g2 : IntegrableOn g2 (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one
  have hint_p0 : IntegrableOn p0 (Ioi (1 : ℝ)) :=
    integrableOn_floor_poly_mul_cpow hs zero_le_one 0 sum_Icc_pow_zero
  have hint_p1 : IntegrableOn p1 (Ioi (1 : ℝ)) :=
    integrableOn_floor_poly_mul_cpow hs (by norm_num) 1 sum_Icc_two_mul_pow_one
  have hint_p2 : IntegrableOn p2 (Ioi (1 : ℝ)) :=
    integrableOn_floor_poly_mul_cpow hs (by norm_num) 2 sum_Icc_six_mul_pow_two
  have hint_p3 : IntegrableOn p3 (Ioi (1 : ℝ)) :=
    integrableOn_floor_poly_mul_cpow hs (by norm_num) 3 sum_Icc_four_mul_pow_three
  have hcongr : EqOn
      (fun t : ℝ ↦ (((t - ⌊t⌋₊) ^ 2 * (1 - (t - ⌊t⌋₊)) ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 4)))
      (fun t : ℝ ↦ g0 t - 2 * g1 t + g2 t - 4 * p0 t + 6 * p1 t - 2 * p2 t + p3 t)
      (Ioi (1 : ℝ)) := by
    intro t ht
    dsimp only [g0, g1, g2, p0, p1, p2, p3]
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (zero_lt_one.trans ht).ne'
    have hp0 : (t : ℂ) ^ (-s) = (t : ℂ) ^ (4 : ℕ) * (t : ℂ) ^ (-(s + 4)) := by
      rw [← cpow_natCast, ← cpow_add _ _ ht0]
      ring_nf
    have hp1 : (t : ℂ) ^ (-(s + 1)) = (t : ℂ) ^ (3 : ℕ) * (t : ℂ) ^ (-(s + 4)) := by
      rw [← cpow_natCast, ← cpow_add _ _ ht0]
      ring_nf
    have hp2 : (t : ℂ) ^ (-(s + 2)) = (t : ℂ) ^ (2 : ℕ) * (t : ℂ) ^ (-(s + 4)) := by
      rw [← cpow_natCast, ← cpow_add _ _ ht0]
      ring_nf
    have hp3 : (t : ℂ) ^ (-(s + (2 : ℕ) + 1)) = (t : ℂ) * (t : ℂ) ^ (-(s + 4)) := by
      rw [show (t : ℂ) * (t : ℂ) ^ (-(s + 4)) = (t : ℂ) ^ (1 : ℂ) * (t : ℂ) ^ (-(s + 4)) by
        rw [cpow_one], ← cpow_add _ _ ht0]
      push_cast
      ring_nf
    have hp0' : (t : ℂ) ^ (-(s + (0 : ℕ) + 1)) = (t : ℂ) ^ (3 : ℕ) * (t : ℂ) ^ (-(s + 4)) := by
      rw [← cpow_natCast, ← cpow_add _ _ ht0]
      push_cast
      ring_nf
    have hp1' : (t : ℂ) ^ (-(s + (1 : ℕ) + 1)) = (t : ℂ) ^ (2 : ℕ) * (t : ℂ) ^ (-(s + 4)) := by
      rw [← cpow_natCast, ← cpow_add _ _ ht0]
      push_cast
      ring_nf
    have hp3' : (t : ℂ) ^ (-(s + (3 : ℕ) + 1)) = (t : ℂ) ^ (-(s + 4)) := by
      push_cast
      ring_nf
    rw [hp0, hp1, hp2, hp0', hp1', hp3, hp3']
    push_cast
    ring
  rw [mellin_quarticKernel_neg_add_three_eq, setIntegral_congr_fun measurableSet_Ioi hcongr]
  have h1 : IntegrableOn (fun x ↦ g0 x - 2 * g1 x) (Ioi (1 : ℝ)) :=
    hint_g0.sub (hint_g1.const_mul 2)
  have h2 : IntegrableOn (fun x ↦ g0 x - 2 * g1 x + g2 x) (Ioi (1 : ℝ)) :=
    h1.add hint_g2
  have h3 : IntegrableOn (fun x ↦ g0 x - 2 * g1 x + g2 x - 4 * p0 x) (Ioi (1 : ℝ)) :=
    h2.sub (hint_p0.const_mul 4)
  have h4 : IntegrableOn (fun x ↦ g0 x - 2 * g1 x + g2 x - 4 * p0 x + 6 * p1 x) (Ioi (1 : ℝ)) :=
    h3.add (hint_p1.const_mul 6)
  have h5 : IntegrableOn (fun x ↦ g0 x - 2 * g1 x + g2 x - 4 * p0 x + 6 * p1 x - 2 * p2 x)
      (Ioi (1 : ℝ)) :=
    h4.sub (hint_p2.const_mul 2)
  rw [integral_add h5 hint_p3,
    integral_sub h4 (hint_p2.const_mul 2),
    integral_add h3 (hint_p1.const_mul 6),
    integral_sub h2 (hint_p0.const_mul 4),
    integral_add h1 hint_g2,
    integral_sub hint_g0 (hint_g1.const_mul 2),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  have hg0_eq : ∫ t in Ioi (1 : ℝ), g0 t = 1 / (s - 1) := by
    dsimp only [g0]
    have h := integral_Ioi_one_cpow_neg_add_one (z := s - 1) (by simp; linarith)
    simpa [sub_add_cancel] using h
  have hg1_eq : ∫ t in Ioi (1 : ℝ), g1 t = 1 / s :=
    integral_Ioi_one_cpow_neg_add_one (by linarith)
  have hg2_eq : ∫ t in Ioi (1 : ℝ), g2 t = 1 / (s + 1) := by
    dsimp only [g2]
    have h := integral_Ioi_one_cpow_neg_add_one (z := s + 1)
      (by simp only [add_re, one_re]; linarith)
    simpa [show s + 1 + 1 = s + 2 by ring] using h
  have hp0_eq := integral_floor_poly_mul_cpow_eq hs zero_le_one 0 sum_Icc_pow_zero
  have hp1_eq := integral_floor_poly_mul_cpow_eq hs (by norm_num) 1 sum_Icc_two_mul_pow_one
  have hp2_eq := integral_floor_poly_mul_cpow_eq hs (by norm_num) 2 sum_Icc_six_mul_pow_two
  have hp3_eq := integral_floor_poly_mul_cpow_eq hs (by norm_num) 3 sum_Icc_four_mul_pow_three
  change _ = _
  rw [hg0_eq, hg1_eq, hg2_eq, hp0_eq, hp1_eq, hp2_eq, hp3_eq]
  have hs1_ne : s - 1 ≠ 0 := sub_ne_zero.mpr (by
    intro h; have := congrArg Complex.re h; norm_num at this; linarith)
  have hs0_ne : s ≠ 0 := by
    intro h; have := congrArg Complex.re h; norm_num at this; linarith
  have hsa1_ne : s + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; norm_num [Complex.add_re] at this; linarith
  have hsa2_ne : s + 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; norm_num [Complex.add_re] at this; linarith
  have hsa3_ne : s + 3 ≠ 0 := by
    intro h; have := congrArg Complex.re h; norm_num [Complex.add_re] at this; linarith
  push_cast
  field_simp [hs1_ne, hs0_ne, hsa1_ne, hsa2_ne, hsa3_ne]
  ring

/-- The open right half-plane `{z : ℂ | 0 < z.re}` is preconnected. -/
theorem isPreconnected_re_pos : IsPreconnected {z : ℂ | 0 < z.re} := by
  have hConv : Convex ℝ {z : ℂ | 0 < z.re} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq, add_re, smul_re, smul_eq_mul] at hx hy ⊢
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · simp only [zero_mul, zero_add] at hab ⊢
      subst hab
      simpa using hy
    · have : 0 < a * x.re := mul_pos ha_pos hx
      have : 0 ≤ b * y.re := mul_nonneg hb hy.le
      linarith
  exact hConv.isPreconnected

/-- **Analytic Continuation of the Fourth-Order Euler–Maclaurin Identity to `0 < s.re`**:
For every `s : ℂ` with `0 < s.re` and `s ≠ 1`,
$$(s - 1) \operatorname{mellin}\;\text{quarticKernel}\;(-(s + 3))
  = \frac{2}{s (s + 1)} - \frac{24}{s (s + 1) (s + 2) (s + 3)} \text{riemannZeta}_1(s).$$ -/
theorem sub_one_mul_mellin_quarticKernel_eq_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    (s - 1) * mellin quarticKernel (-(s + 3)) =
      2 / (s * (s + 1)) -
        24 / (s * (s + 1) * (s + 2) * (s + 3)) * riemannZeta₁ s := by
  have hOpen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hAn1 : AnalyticOnNhd ℂ (fun z : ℂ ↦ (z - 1) * mellin quarticKernel (-(z + 3)))
      {z : ℂ | 0 < z.re} := by
    refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) hOpen
    refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.mul ?_ ?_)
    · exact differentiableAt_id.sub_const 1
    · exact (differentiableAt_mellin_quarticKernel
        (by simp only [neg_re, add_re]; norm_num; linarith [show 0 < z.re from hz])).comp z
        (differentiableAt_id.add_const 3).neg
  have hAn2 : AnalyticOnNhd ℂ
      (fun z : ℂ ↦ 2 / (z * (z + 1)) -
        24 / (z * (z + 1) * (z + 2) * (z + 3)) * riemannZeta₁ z)
      {z : ℂ | 0 < z.re} := by
    refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) hOpen
    have hz0 : z ≠ 0 := by intro h; subst h; simp at hz
    have hz1 : z + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h
      norm_num [Complex.add_re] at this; linarith [show 0 < z.re from hz]
    have hz2 : z + 2 ≠ 0 := by
      intro h; have := congrArg Complex.re h
      norm_num [Complex.add_re] at this; linarith [show 0 < z.re from hz]
    have hz3 : z + 3 ≠ 0 := by
      intro h; have := congrArg Complex.re h
      norm_num [Complex.add_re] at this; linarith [show 0 < z.re from hz]
    refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.sub ?_ ?_)
    · exact (differentiableAt_const 2).div
        (differentiableAt_id.mul (differentiableAt_id.add_const 1)) (mul_ne_zero hz0 hz1)
    · refine DifferentiableAt.mul ?_ (differentiable_riemannZeta₁ z)
      exact (differentiableAt_const 24).div
        (((differentiableAt_id.mul (differentiableAt_id.add_const 1)).mul
          (differentiableAt_id.add_const 2)).mul (differentiableAt_id.add_const 3))
        (mul_ne_zero (mul_ne_zero (mul_ne_zero hz0 hz1) hz2) hz3)
  have hEv : (fun z : ℂ ↦ (z - 1) * mellin quarticKernel (-(z + 3))) =ᶠ[𝓝 (2 : ℂ)]
      (fun z : ℂ ↦ 2 / (z * (z + 1)) -
        24 / (z * (z + 1) * (z + 2) * (z + 3)) * riemannZeta₁ z) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    have hz1 : z ≠ 1 := by intro h; subst h; simp at hz
    have hz1_sub : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    have hzeta1 : riemannZeta₁ z = (z - 1) * riemannZeta z := by
      rw [riemannZeta_eq_inv_sub_mul hz1, ← mul_assoc, mul_inv_cancel₀ hz1_sub, one_mul]
    rw [mellin_quarticKernel_neg_add_three_eq_of_one_lt_re hz, hzeta1]
    field_simp [hz1_sub]
  exact hAn1.eqOn_of_preconnected_of_eventuallyEq hAn2 isPreconnected_re_pos
    (by norm_num : (2 : ℂ) ∈ _) hEv hs

/-- At any zero `ρ` of `riemannZeta` with `0 < ρ.re`,
`mellin quarticKernel (-(ρ + 3)) = 2 / ((ρ - 1) * ρ * (ρ + 1))`. -/
theorem mellin_quarticKernel_eq_of_riemannZeta_eq_zero {ρ : ℂ}
    (hρ : 0 < ρ.re) (hζ : riemannZeta ρ = 0) :
    mellin quarticKernel (-(ρ + 3)) = 2 / ((ρ - 1) * ρ * (ρ + 1)) := by
  have hρ1 : ρ ≠ 1 := by
    rintro rfl
    exact riemannZeta_one_ne_zero hζ
  have hρ1_sub : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  have hζ₁ : riemannZeta₁ ρ = 0 := by
    have h := riemannZeta_eq_inv_sub_mul hρ1
    rw [hζ] at h
    rcases mul_eq_zero.mp h.symm with hinv | h1
    · exact absurd hinv (inv_ne_zero hρ1_sub)
    · exact h1
  have hid := sub_one_mul_mellin_quarticKernel_eq_of_re_pos hρ
  rw [hζ₁, mul_zero, sub_zero] at hid
  apply mul_left_cancel₀ hρ1_sub
  rw [hid]
  field_simp [hρ1_sub]

/-- Explicit antiderivative of `(t - 1) ^ 2 * (2 - t) ^ 2 * t ^ (-9 / 2 : ℝ)` on `(0, ∞)`. -/
noncomputable def quarticIocAntideriv (t : ℝ) : ℝ :=
  2 * t ^ (1 / 2 : ℝ) + 12 * t ^ (-1 / 2 : ℝ) - (26 / 3) * t ^ (-3 / 2 : ℝ) +
    (24 / 5) * t ^ (-5 / 2 : ℝ) - (8 / 7) * t ^ (-7 / 2 : ℝ)

/-- For `0 < t`,
`HasDerivAt quarticIocAntideriv ((t - 1) ^ 2 * (2 - t) ^ 2 * t ^ (-9 / 2 : ℝ)) t`. -/
theorem hasDerivAt_quarticIocAntideriv {t : ℝ} (ht : 0 < t) :
    HasDerivAt quarticIocAntideriv ((t - 1) ^ 2 * (2 - t) ^ 2 * t ^ (-9 / 2 : ℝ)) t := by
  unfold quarticIocAntideriv
  have h1 := (Real.hasDerivAt_rpow_const (p := (1 / 2 : ℝ)) (Or.inl ht.ne')).const_mul 2
  have h2 := (Real.hasDerivAt_rpow_const (p := (-1 / 2 : ℝ)) (Or.inl ht.ne')).const_mul 12
  have h3 := (Real.hasDerivAt_rpow_const (p := (-3 / 2 : ℝ)) (Or.inl ht.ne')).const_mul (26 / 3)
  have h4 := (Real.hasDerivAt_rpow_const (p := (-5 / 2 : ℝ)) (Or.inl ht.ne')).const_mul (24 / 5)
  have h5 := (Real.hasDerivAt_rpow_const (p := (-7 / 2 : ℝ)) (Or.inl ht.ne')).const_mul (8 / 7)
  refine ((((h1.add h2).sub h3).add h4).sub h5).congr_deriv ?_
  have p1 : t ^ ((1 / 2 : ℝ) - 1) = t ^ (4 : ℕ) * t ^ (-9 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht]
    norm_num
  have p2 : t ^ ((-1 / 2 : ℝ) - 1) = t ^ (3 : ℕ) * t ^ (-9 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht]
    norm_num
  have p3 : t ^ ((-3 / 2 : ℝ) - 1) = t ^ (2 : ℕ) * t ^ (-9 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht]
    norm_num
  have p4 : t ^ ((-5 / 2 : ℝ) - 1) = t * t ^ (-9 / 2 : ℝ) := by
    have h := (Real.rpow_add ht (1 : ℝ) (-9 / 2 : ℝ)).symm
    rw [Real.rpow_one] at h
    rw [h]
    norm_num
  have p5 : t ^ ((-7 / 2 : ℝ) - 1) = t ^ (-9 / 2 : ℝ) := by norm_num
  rw [p1, p2, p3, p4, p5]
  ring

/-- Exact evaluation of `∫ t in Ioc 1 2, (t - 1) ^ 2 * (2 - t) ^ 2 * t ^ (-9 / 2 : ℝ)`
and the rational upper bound `≤ 1 / 150`. -/
theorem integral_Ioc_one_two_quartic_le :
    (∫ t in Ioc (1 : ℝ) 2, (t - 1) ^ 2 * (2 - t) ^ 2 * t ^ (-9 / 2 : ℝ)) ≤ 1 / 150 := by
  have hle : (1 : ℝ) ≤ 2 := by norm_num
  rw [← intervalIntegral.integral_of_le hle]
  have hderiv : ∀ t ∈ Set.uIcc (1 : ℝ) 2,
      HasDerivAt quarticIocAntideriv ((t - 1) ^ 2 * (2 - t) ^ 2 * t ^ (-9 / 2 : ℝ)) t := by
    intro t ht
    rw [Set.uIcc_of_le hle] at ht
    exact hasDerivAt_quarticIocAntideriv (zero_lt_one.trans_le ht.1)
  have hint : IntervalIntegrable
      (fun t : ℝ ↦ (t - 1) ^ 2 * (2 - t) ^ 2 * t ^ (-9 / 2 : ℝ)) volume 1 2 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle]
    refine (continuousOn_of_forall_continuousAt fun t ht ↦ ?_).integrableOn_Icc
    have ht_pos : 0 < t := zero_lt_one.trans_le ht.1
    refine ContinuousAt.mul ?_ (Real.continuousAt_rpow_const _ _ (Or.inl ht_pos.ne'))
    exact ((continuousAt_id.sub continuousAt_const).pow 2).mul
      ((continuousAt_const.sub continuousAt_id).pow 2)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  unfold quarticIocAntideriv
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have r1 : (2 : ℝ) ^ (-1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℤ) * (2 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_intCast, ← Real.rpow_add h2_pos]
    norm_num
  have r2 : (2 : ℝ) ^ (-3 / 2 : ℝ) = (2 : ℝ) ^ (-2 : ℤ) * (2 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_intCast, ← Real.rpow_add h2_pos]
    norm_num
  have r3 : (2 : ℝ) ^ (-5 / 2 : ℝ) = (2 : ℝ) ^ (-3 : ℤ) * (2 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_intCast, ← Real.rpow_add h2_pos]
    norm_num
  have r4 : (2 : ℝ) ^ (-7 / 2 : ℝ) = (2 : ℝ) ^ (-4 : ℤ) * (2 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_intCast, ← Real.rpow_add h2_pos]
    norm_num
  rw [r1, r2, r3, r4, ← Real.sqrt_eq_rpow]
  simp only [Real.one_rpow]
  have hsqrt2 : 6680 * Real.sqrt 2 ≤ 9447 := by
    rw [← abs_of_nonneg (by positivity : 0 ≤ 6680 * Real.sqrt 2),
      ← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9447), ← sq_le_sq,
      mul_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  linarith

/-- Explicit tail bound on `Ioi 2`:
`∫ t in Ioi 2, (1 / 16 : ℝ) * t ^ (-9 / 2 : ℝ) ≤ 1 / 600`. -/
theorem integral_Ioi_two_quartic_tail_le :
    (∫ t in Ioi (2 : ℝ), (1 / 16 : ℝ) * t ^ (-9 / 2 : ℝ)) ≤ 1 / 600 := by
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)]
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have hrpow : (2 : ℝ) ^ ((-9 / 2 : ℝ) + 1) = (1 / 16 : ℝ) * Real.sqrt 2 := by
    have h16 : (1 / 16 : ℝ) = (2 : ℝ) ^ (-4 : ℤ) := by norm_num
    rw [h16, Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_add h2_pos]
    norm_num
  rw [hrpow]
  have h_eq : (1 / 16 : ℝ) * (-((1 / 16 : ℝ) * Real.sqrt 2) / ((-9 / 2 : ℝ) + 1)) =
      (1 / 896) * Real.sqrt 2 := by ring
  rw [h_eq]
  have hsqrt2 : 75 * Real.sqrt 2 ≤ 112 := by
    rw [← abs_of_nonneg (by positivity : 0 ≤ 75 * Real.sqrt 2),
      ← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 112), ← sq_le_sq,
      mul_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  linarith

/-- **Critical-Line Norm Bound on `mellin quarticKernel (-(s + 3))`**:
For any `s : ℂ` with `s.re = 1 / 2`,
`‖mellin quarticKernel (-(s + 3))‖ ≤ 1 / 120`. -/
theorem norm_mellin_quarticKernel_le_of_re_eq_half {s : ℂ} (hre : s.re = 1 / 2) :
    ‖mellin quarticKernel (-(s + 3))‖ ≤ 1 / 120 := by
  rw [mellin_quarticKernel_neg_add_three_eq]
  let f : ℝ → ℝ := fun t ↦ (t - (⌊t⌋₊ : ℝ)) ^ 2 * (1 - (t - (⌊t⌋₊ : ℝ))) ^ 2 * t ^ (-9 / 2 : ℝ)
  have hf_meas : AEStronglyMeasurable f (volume.restrict (Ioi (1 : ℝ))) := by
    have hm1 : Measurable (fun t : ℝ ↦ t - (⌊t⌋₊ : ℝ)) :=
      measurable_id.sub (measurable_from_nat.comp Nat.measurable_floor)
    have hm2 : Measurable (fun t : ℝ ↦ (t - (⌊t⌋₊ : ℝ)) ^ 2 * (1 - (t - (⌊t⌋₊ : ℝ))) ^ 2) :=
      (hm1.pow_const 2).mul ((measurable_const.sub hm1).pow_const 2)
    refine AEStronglyMeasurable.mul hm2.aestronglyMeasurable ?_
    refine (continuousOn_of_forall_continuousAt fun t ht ↦ ?_).aestronglyMeasurable
      measurableSet_Ioi
    exact Real.continuousAt_rpow_const _ _ (Or.inl (zero_lt_one.trans ht).ne')
  have hf_int : IntegrableOn f (Ioi (1 : ℝ)) := by
    refine ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-9 / 2 : ℝ) < -1) zero_lt_one).const_mul
      (1 / 16)).mono' hf_meas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht_pos : 0 < t := zero_lt_one.trans ht
    obtain ⟨h0, h1⟩ := quartic_floor_bounds ht_pos.le
    dsimp only [f]
    rw [Real.norm_of_nonneg (mul_nonneg h0 (Real.rpow_nonneg ht_pos.le _))]
    exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht_pos.le _)
  have hnorm_le :
      ‖∫ t in Ioi (1 : ℝ),
        (((t - ⌊t⌋₊) ^ 2 * (1 - (t - ⌊t⌋₊)) ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 4))‖ ≤
      ∫ t in Ioi (1 : ℝ), f t := by
    refine norm_integral_le_of_norm_le hf_int ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht_pos : 0 < t := zero_lt_one.trans ht
    obtain ⟨h0, _⟩ := quartic_floor_bounds ht_pos.le
    rw [norm_mul, norm_real, Real.norm_of_nonneg h0, norm_cpow_eq_rpow_re_of_pos ht_pos]
    have hexp : (-(s + 4)).re = -9 / 2 := by simp [hre]; ring
    rw [hexp]
  have hunion : Ioi (1 : ℝ) = Ioc (1 : ℝ) 2 ∪ Ioi (2 : ℝ) :=
    (Ioc_union_Ioi_eq_Ioi (by norm_num : (1 : ℝ) ≤ 2)).symm
  have hdisj : Disjoint (Ioc (1 : ℝ) 2) (Ioi (2 : ℝ)) := Ioc_disjoint_Ioi le_rfl
  have hsplit : ∫ t in Ioi (1 : ℝ), f t =
      (∫ t in Ioc (1 : ℝ) 2, f t) + ∫ t in Ioi (2 : ℝ), f t := by
    rw [hunion, setIntegral_union hdisj measurableSet_Ioi
      (hf_int.mono_set (by rw [hunion]; exact subset_union_left))
      (hf_int.mono_set (by rw [hunion]; exact subset_union_right))]
  have h_ioc : ∫ t in Ioc (1 : ℝ) 2, f t ≤ 1 / 150 := by
    have h_ae : f =ᵐ[volume.restrict (Ioc (1 : ℝ) 2)]
        fun t : ℝ ↦ (t - 1) ^ 2 * (2 - t) ^ 2 * t ^ (-9 / 2 : ℝ) := by
      have h_eq_ioo : EqOn f (fun t : ℝ ↦ (t - 1) ^ 2 * (2 - t) ^ 2 * t ^ (-9 / 2 : ℝ))
          (Ioo (1 : ℝ) 2) := by
        intro t ht
        dsimp only [f]
        have hfl : ⌊t⌋₊ = 1 :=
          Nat.floor_eq_iff (zero_lt_one.trans ht.1).le |>.mpr
            ⟨by exact_mod_cast ht.1.le, by norm_num; exact ht.2⟩
        rw [hfl, Nat.cast_one]
        ring
      exact (ae_restrict_iff' measurableSet_Ioc).mpr
        (ae_of_all _ fun t ht ↦ by
          rcases eq_or_lt_of_le ht.2 with rfl | hlt
          · simp [f]
          · exact h_eq_ioo ⟨ht.1, hlt⟩)
    rw [integral_congr_ae h_ae]
    exact integral_Ioc_one_two_quartic_le
  have h_ioi : ∫ t in Ioi (2 : ℝ), f t ≤ 1 / 600 := by
    refine ( setIntegral_mono_on (hf_int.mono_set (Ioi_subset_Ioi (by norm_num)))
      ((integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).const_mul (1 / 16))
      measurableSet_Ioi fun t ht ↦ ?_ ).trans integral_Ioi_two_quartic_tail_le
    have ht_pos : 0 < t := by linarith [mem_Ioi.mp ht]
    obtain ⟨_, h1⟩ := quartic_floor_bounds ht_pos.le
    exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht_pos.le _)
  linarith

/-- **Fourth-Order Critical-Line Product Bound (`240 ≤ ‖ρ - 1‖ * ‖ρ‖ * ‖ρ + 1‖`)**:
For every zero `ρ` of `riemannZeta` with `ρ.re = 1 / 2`,
`240 ≤ ‖ρ - 1‖ * ‖ρ‖ * ‖ρ + 1‖`. -/
theorem two_hundred_forty_le_norm_prod_of_riemannZeta_eq_zero_of_re_eq_half {ρ : ℂ}
    (hre : ρ.re = 1 / 2) (hζ : riemannZeta ρ = 0) :
    240 ≤ ‖ρ - 1‖ * ‖ρ‖ * ‖ρ + 1‖ := by
  have hρ_pos : 0 < ρ.re := by linarith
  have h_eq := mellin_quarticKernel_eq_of_riemannZeta_eq_zero hρ_pos hζ
  have h_le := norm_mellin_quarticKernel_le_of_re_eq_half hre
  rw [h_eq, norm_div, norm_ofNat, norm_mul, norm_mul] at h_le
  have h1 : 0 < ‖ρ - 1‖ := norm_pos_iff.mpr (by
    intro h; have := congrArg Complex.re (sub_eq_zero.mp h); simp [hre] at this)
  have h2 : 0 < ‖ρ‖ := norm_pos_iff.mpr (by
    intro h; rw [h] at hre; simp at hre)
  have h3 : 0 < ‖ρ + 1‖ := norm_pos_iff.mpr (by
    intro h; have := congrArg Complex.re h; simp [hre] at this; linarith)
  have hprod_pos : 0 < ‖ρ - 1‖ * ‖ρ‖ * ‖ρ + 1‖ := mul_pos (mul_pos h1 h2) h3
  rw [div_le_iff₀ hprod_pos] at h_le
  linarith

/-- **Low-Lying Zero-Free Region on the Critical Line (`37 < ρ.im ^ 2`)**:
For every zero `ρ` of `riemannZeta` with `ρ.re = 1 / 2`, `37 < ρ.im ^ 2`. -/
theorem thirty_seven_lt_im_sq_of_riemannZeta_eq_zero_of_re_eq_half {ρ : ℂ}
    (hre : ρ.re = 1 / 2) (hζ : riemannZeta ρ = 0) :
    37 < ρ.im ^ 2 := by
  have hprod := two_hundred_forty_le_norm_prod_of_riemannZeta_eq_zero_of_re_eq_half hre hζ
  have h_norm_sq : ‖ρ‖ ^ 2 = 1 / 4 + ρ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre]
    ring
  have h_norm_sub_eq : ‖ρ - 1‖ = ‖ρ‖ := by
    apply sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mp
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [sub_re, one_re, sub_im, one_im, hre]
    ring
  have h_norm_add_sq : ‖ρ + 1‖ ^ 2 = 9 / 4 + ρ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [add_re, one_re, add_im, one_im, hre]
    ring
  rw [h_norm_sub_eq, ← sq, h_norm_sq] at hprod
  have hsq : 240 ^ 2 ≤ ((1 / 4 + ρ.im ^ 2) * ‖ρ + 1‖) ^ 2 := by
    nlinarith [norm_nonneg (ρ + 1)]
  rw [mul_pow, h_norm_add_sq] at hsq
  by_contra! hle
  have hnonneg : 0 ≤ ρ.im ^ 2 := sq_nonneg ρ.im
  nlinarith

/-- **Low-Lying Zero-Free Region on the Critical Line (`6 < |ρ.im|`)**:
For every zero `ρ` of `riemannZeta` with `ρ.re = 1 / 2`, `6 < |ρ.im|`. -/
theorem six_lt_abs_im_of_riemannZeta_eq_zero_of_re_eq_half {ρ : ℂ}
    (hre : ρ.re = 1 / 2) (hζ : riemannZeta ρ = 0) :
    6 < |ρ.im| := by
  have h := thirty_seven_lt_im_sq_of_riemannZeta_eq_zero_of_re_eq_half hre hζ
  rw [← sq_abs] at h
  by_contra! hle
  have hnonneg : 0 ≤ |ρ.im| := abs_nonneg ρ.im
  nlinarith

/-- A complex number `s` is a nontrivial zero of `riemannZeta` if `riemannZeta s = 0`,
`s` is not a trivial zero `-2 * (n + 1)` (`n : ℕ`), and `s ≠ 1`. -/
def IsNontrivialZetaZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ (¬∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1

/-- No nontrivial zero of `riemannZeta` equals `0`. -/
theorem isNontrivialZetaZero_ne_zero {s : ℂ} (hs : IsNontrivialZetaZero s) : s ≠ 0 := by
  rintro rfl
  have h0 := hs.1
  rw [riemannZeta_zero] at h0
  norm_num at h0

/-- Every nontrivial zero `s` of `riemannZeta` has `s.re < 1`. -/
theorem re_lt_one_of_isNontrivialZetaZero {s : ℂ} (hs : IsNontrivialZetaZero s) : s.re < 1 := by
  by_contra! hle
  exact riemannZeta_ne_zero_of_one_le_re hle hs.1

/-- Every nontrivial zero `s` of `riemannZeta` has `0 < s.re`. -/
theorem zero_lt_re_of_isNontrivialZetaZero {s : ℂ} (hs : IsNontrivialZetaZero s) : 0 < s.re := by
  by_contra! hle
  have hs0 : s ≠ 0 := isNontrivialZetaZero_ne_zero hs
  have h1s_re : 1 ≤ (1 - s).re := by simp [hle]
  have h1s_ne_neg_nat : ∀ n : ℕ, 1 - s ≠ -n := by
    intro n heq
    have hre := congrArg Complex.re heq
    simp at hre
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h1s_ne_one : 1 - s ≠ 1 := by simpa using hs0
  have hfe := riemannZeta_one_sub h1s_ne_neg_nat h1s_ne_one
  rw [sub_sub_cancel, hs.1] at hfe
  have h2pi : (2 * π : ℂ) ^ (-(1 - s)) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    left
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have hGamma : Gamma (1 - s) ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have hZeta : riemannZeta (1 - s) ≠ 0 := riemannZeta_ne_zero_of_one_le_re h1s_re
  have hcos : cos (π * (1 - s) / 2) = 0 := by
    rcases mul_eq_zero.mp hfe.symm with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · rcases mul_eq_zero.mp h with h | h
          · norm_num at h
          · exact absurd h h2pi
        · exact absurd h hGamma
      · exact h
    · exact absurd h hZeta
  rw [cos_eq_zero_iff] at hcos
  obtain ⟨k, hk⟩ := hcos
  have hpi_ne : (π : ℂ) ≠ 0 := mod_cast Real.pi_ne_zero
  have h1s_eq : 1 - s = 2 * k + 1 := by
    apply mul_right_cancel₀ hpi_ne
    calc
      (1 - s) * π = (π * (1 - s) / 2) * 2 := by ring
      _ = ((2 * k + 1) * π / 2) * 2 := by rw [hk]
      _ = (2 * k + 1) * π := by ring
  have hs_eq : s = -2 * (k : ℂ) := by linear_combination -h1s_eq
  have hk_re : (k : ℝ) ≥ 0 := by
    have hre := congrArg Complex.re hs_eq
    simp at hre
    linarith
  have hk_int : 0 ≤ k := by exact_mod_cast hk_re
  have hk_ne_zero : k ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, mul_zero] at hs_eq
    exact hs0 hs_eq
  refine hs.2.1 ⟨(k - 1).toNat, ?_⟩
  have hk_nat : ((k - 1).toNat : ℂ) + 1 = (k : ℂ) := by
    have : ((k - 1).toNat : ℤ) + 1 = k := by omega
    exact_mod_cast this
  rw [hk_nat, hs_eq]

/-- Every nontrivial zero of `riemannZeta` satisfies `0 < s.re ∧ s.re < 1`. -/
theorem mem_criticalStrip_of_isNontrivialZetaZero {s : ℂ} (hs : IsNontrivialZetaZero s) :
    0 < s.re ∧ s.re < 1 :=
  ⟨zero_lt_re_of_isNontrivialZetaZero hs, re_lt_one_of_isNontrivialZetaZero hs⟩

/-- Finiteness of nontrivial zeros up to height `T`. -/
theorem finite_nontrivialZetaZeros_le (T : ℝ) :
    {s : ℂ | IsNontrivialZetaZero s ∧ |s.im| ≤ T}.Finite := by
  have hcompact : IsCompact (Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc (-T) T) :=
    isCompact_Icc.reProdIm isCompact_Icc
  refine (hcompact.inter_riemannZetaZeros_finite).subset ?_
  rintro s ⟨hs, him⟩
  obtain ⟨hre0, hre1⟩ := mem_criticalStrip_of_isNontrivialZetaZero hs
  refine ⟨⟨⟨hre0.le, hre1.le⟩, abs_le.mp him⟩, hs.1⟩

/-- The canonical `Finset ℂ` of nontrivial zeros of `riemannZeta` with `|s.im| ≤ T`. -/
noncomputable def nontrivialZetaZerosUpTo (T : ℝ) : Finset ℂ :=
  (finite_nontrivialZetaZeros_le T).toFinset

@[simp]
theorem mem_nontrivialZetaZerosUpTo {T : ℝ} {s : ℂ} :
    s ∈ nontrivialZetaZerosUpTo T ↔ IsNontrivialZetaZero s ∧ |s.im| ≤ T :=
  Set.Finite.mem_toFinset (finite_nontrivialZetaZeros_le T)

/-- Under `RiemannHypothesis`, every nontrivial zero `ρ` of `riemannZeta` satisfies
`6 < |ρ.im|`. -/
theorem six_lt_abs_im_of_riemannHypothesis (hRH : RiemannHypothesis) {ρ : ℂ}
    (hρ : IsNontrivialZetaZero ρ) :
    6 < |ρ.im| :=
  six_lt_abs_im_of_riemannZeta_eq_zero_of_re_eq_half (hRH ρ hρ.1 hρ.2.1 hρ.2.2) hρ.1

end ConjectureMachines.Semantics.Riemann.VonMangoldtCount
