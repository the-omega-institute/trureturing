/- GID: D5/S3/Weil/Scattering/BodeWidthCriterion
   generality: G
   mirror-B: D5/B/S3/Weil/Scattering/BodeWidthCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite mirror pairs have equal width-area, curvature, and line defects. -/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

namespace D5.S3.Weil.Scattering.BodeWidthCriterion

open scoped BigOperators Interval
open MeasureTheory Set

private lemma triangular_pulse_integrable (d : ℝ) :
    Integrable (fun y : ℝ => max (d - |y - 1 / 2|) 0) := by
  let f := fun y : ℝ => max (d - |y - 1 / 2|) 0
  have hf : Continuous f :=
    (continuous_const.sub (continuous_id.sub continuous_const).abs).max continuous_const
  have hsupp : Function.support f ⊆ Icc (1 / 2 - d) (1 / 2 + d) := by
    apply Function.support_subset_iff'.2
    intro y hy
    simp only [mem_Icc, not_and_or] at hy
    rcases hy with hy | hy
    · have habs : d ≤ |y - 1 / 2| :=
        le_trans (by linarith) (neg_le_abs (y - 1 / 2))
      simp only [f]
      apply max_eq_right
      exact sub_nonpos.2 habs
    · have habs : d ≤ |y - 1 / 2| :=
        le_trans (by linarith) (le_abs_self (y - 1 / 2))
      simp only [f]
      apply max_eq_right
      exact sub_nonpos.2 habs
  exact (integrableOn_iff_integrable_of_support_subset hsupp).1 hf.integrableOn_Icc

private lemma triangular_pulse_integral (d : ℝ) (hd : 0 ≤ d) (hhalf : d ≤ 1 / 2) :
    ∫ y in Ioi (0 : ℝ), max (d - |y - 1 / 2|) 0 = d ^ 2 := by
  let f := fun y : ℝ => max (d - |y - 1 / 2|) 0
  have hf : Integrable f := triangular_pulse_integrable d
  have htail : ∫ y in Ioi (1 / 2 + d), f y = 0 := by
    calc
      ∫ y in Ioi (1 / 2 + d), f y = ∫ _y in Ioi (1 / 2 + d), (0 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y hy
        change 1 / 2 + d < y at hy
        change max (d - |y - 1 / 2|) 0 = 0
        have habs : d ≤ |y - 1 / 2| :=
          le_trans (by linarith [hy]) (le_abs_self (y - 1 / 2))
        rw [max_eq_right (sub_nonpos.2 habs)]
      _ = 0 := by simp
  have hleft : ∫ y in (0 : ℝ)..(1 / 2 - d), f y = 0 := by
    calc
      ∫ y in (0 : ℝ)..(1 / 2 - d), f y = ∫ _y in (0 : ℝ)..(1 / 2 - d), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [uIcc_of_le (by linarith)] at hy
        change max (d - |y - 1 / 2|) 0 = 0
        have habs : d ≤ |y - 1 / 2| :=
          le_trans (by linarith [hy.2]) (neg_le_abs (y - 1 / 2))
        rw [max_eq_right (sub_nonpos.2 habs)]
      _ = 0 := by simp
  have hrise :
      ∫ y in (1 / 2 - d)..(1 / 2), f y =
        ∫ y in (1 / 2 - d)..(1 / 2), (y - (1 / 2 - d)) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le (by linarith)] at hy
    change max (d - |y - 1 / 2|) 0 = y - (1 / 2 - d)
    rw [abs_of_nonpos (by linarith [hy.2]), max_eq_left (by linarith [hy.1])]
    ring
  have hfall :
      ∫ y in (1 / 2)..(1 / 2 + d), f y =
        ∫ y in (1 / 2)..(1 / 2 + d), ((1 / 2 + d) - y) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le (by linarith)] at hy
    change max (d - |y - 1 / 2|) 0 = (1 / 2 + d) - y
    rw [abs_of_nonneg (by linarith [hy.1]), max_eq_left (by linarith [hy.2])]
    ring
  have hrise_value :
      ∫ y in (1 / 2 - d)..(1 / 2), (y - (1 / 2 - d)) = d ^ 2 / 2 := by
    change (∫ y in (1 / 2 - d)..(1 / 2), id y - (1 / 2 - d)) = d ^ 2 / 2
    rw [intervalIntegral.integral_sub (continuous_id.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _)]
    simp [integral_id]
    ring
  have hfall_value :
      ∫ y in (1 / 2)..(1 / 2 + d), ((1 / 2 + d) - y) = d ^ 2 / 2 := by
    change (∫ y in (1 / 2)..(1 / 2 + d), (1 / 2 + d) - id y) = d ^ 2 / 2
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      (continuous_id.intervalIntegrable _ _)]
    simp [integral_id]
    ring
  calc
    ∫ y in Ioi (0 : ℝ), max (d - |y - 1 / 2|) 0 = ∫ y in Ioi (0 : ℝ), f y := rfl
    _ = ∫ y in (0 : ℝ)..(1 / 2 + d), f y := by
      rw [← intervalIntegral.integral_interval_add_Ioi hf.integrableOn
        hf.integrableOn, htail, add_zero]
    _ = (∫ y in (0 : ℝ)..(1 / 2 - d), f y) +
          ∫ y in (1 / 2 - d)..(1 / 2 + d), f y := by
      rw [intervalIntegral.integral_add_adjacent_intervals
        hf.intervalIntegrable hf.intervalIntegrable]
    _ = (∫ y in (1 / 2 - d)..(1 / 2), f y) +
          ∫ y in (1 / 2)..(1 / 2 + d), f y := by
      rw [hleft, zero_add, intervalIntegral.integral_add_adjacent_intervals
        hf.intervalIntegrable hf.intervalIntegrable]
    _ = d ^ 2 := by rw [hrise, hfall, hrise_value, hfall_value]; ring

private lemma damping_second_derivative {ι : Type*} [Fintype ι] (δ : ι → ℝ) :
    deriv (deriv (fun τ : ℝ => ∑ i, 2 * (Real.cosh (τ * δ i) - 1))) 0 =
      2 * ∑ i, (δ i) ^ 2 := by
  let first := fun τ : ℝ => ∑ i, 2 * (Real.sinh (τ * δ i) * δ i)
  have hfirst (τ : ℝ) :
      HasDerivAt (fun τ : ℝ => ∑ i, 2 * (Real.cosh (τ * δ i) - 1)) (first τ) τ := by
    dsimp [first]
    simpa only using HasDerivAt.fun_sum (u := Finset.univ) (x := τ)
      (A' := fun i => 2 * (Real.sinh (τ * δ i) * δ i)) (fun i hi => by
        simpa [mul_assoc] using (((Real.hasDerivAt_cosh (τ * δ i)).comp τ
          ((hasDerivAt_id τ).mul_const (δ i))).sub_const 1).const_mul 2)
  have hderiv :
      deriv (fun τ : ℝ => ∑ i, 2 * (Real.cosh (τ * δ i) - 1)) = first := by
    funext τ
    exact (hfirst τ).deriv
  rw [hderiv]
  have hsecond : HasDerivAt first (2 * ∑ i, (δ i) ^ 2) 0 := by
    dsimp [first]
    simpa only [Finset.mul_sum, Finset.sum_apply] using
      HasDerivAt.fun_sum (u := Finset.univ) (x := (0 : ℝ)) (A' := fun i => 2 * (δ i) ^ 2)
        (fun i hi => by
          simpa [pow_two, mul_assoc] using
            (((Real.hasDerivAt_sinh (0 * δ i)).comp 0
              ((hasDerivAt_id 0).mul_const (δ i))).mul_const (δ i)).const_mul 2)
  exact hsecond.deriv

/-- The critical-line, pointwise-width, area, mirror-displacement, and damping-curvature
conditions coincide for a finite functional-equation-paired resonance family. -/
theorem bode_width_criterion {ι : Type*} [Fintype ι] (δ : ι → ℝ)
    (hδ0 : ∀ i, 0 ≤ δ i) (hδhalf : ∀ i, δ i ≤ 1 / 2) :
    let criticalLine := ∀ i, 1 / 2 + δ i = 1 / 2 ∧ 1 / 2 - δ i = 1 / 2
    let width := fun y : ℝ => ∑ i, max (δ i - |y - 1 / 2|) 0
    let area := ∫ y in Ioi (0 : ℝ), width y
    let resonanceDisplacementSquare :=
      ∑ i, (((1 / 2 + δ i) - 1 / 2) ^ 2 + ((1 / 2 - δ i) - 1 / 2) ^ 2)
    let dampingDefect := fun τ : ℝ => ∑ i, 2 * (Real.cosh (τ * δ i) - 1)
    (criticalLine ↔ ∀ y > 0, width y = 0) ∧
      ((∀ y > 0, width y = 0) ↔ area = 0) ∧
      area = (1 / 2) * resonanceDisplacementSquare ∧
      area = (1 / 2) * deriv (deriv dampingDefect) 0 := by
  dsimp only
  have hpulse_integrable (i : ι) :
      IntegrableOn (fun y : ℝ => max (δ i - |y - 1 / 2|) 0) (Ioi 0) :=
    (triangular_pulse_integrable (δ i)).integrableOn
  have harea :
      (∫ y in Ioi (0 : ℝ), ∑ i, max (δ i - |y - 1 / 2|) 0) = ∑ i, (δ i) ^ 2 := by
    rw [MeasureTheory.integral_finsetSum Finset.univ]
    · apply Finset.sum_congr rfl
      intro i hi
      exact triangular_pulse_integral (δ i) (hδ0 i) (hδhalf i)
    · intro i hi
      exact hpulse_integrable i
  have hcritical_pointwise :
      (∀ i, 1 / 2 + δ i = 1 / 2 ∧ 1 / 2 - δ i = 1 / 2) ↔
        ∀ y > 0, ∑ i, max (δ i - |y - 1 / 2|) 0 = 0 := by
    constructor
    · intro h y hy
      apply Finset.sum_eq_zero
      intro i hi
      have hzero : δ i = 0 := by linarith [(h i).1]
      simp [hzero]
    · intro h
      have hsum : ∑ i, δ i = 0 := by
        have hw := h (1 / 2) (by norm_num)
        norm_num at hw
        simp_rw [max_eq_left (hδ0 _)] at hw
        exact hw
      have hzero : ∀ i, δ i = 0 := by
        intro i
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => hδ0 j)).1 hsum i
          (Finset.mem_univ i)
      intro i
      simp [hzero i]
  have hpointwise_area :
      ((∀ y > 0, ∑ i, max (δ i - |y - 1 / 2|) 0 = 0) ↔
        (∫ y in Ioi (0 : ℝ), ∑ i, max (δ i - |y - 1 / 2|) 0) = 0) := by
    rw [harea]
    constructor
    · intro h
      have hc := hcritical_pointwise.mpr h
      apply Finset.sum_eq_zero
      intro i hi
      have hzero : δ i = 0 := by linarith [(hc i).1]
      simp [hzero]
    · intro h
      have hzero : ∀ i, δ i = 0 := by
        intro i
        have hsquare : (δ i) ^ 2 = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => sq_nonneg (δ j))).1 h i
            (Finset.mem_univ i)
        exact sq_eq_zero_iff.mp hsquare
      intro y hy
      simp [hzero]
  refine ⟨hcritical_pointwise, hpointwise_area, ?_, ?_⟩
  · rw [harea]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · rw [harea, damping_second_derivative]
    ring

end D5.S3.Weil.Scattering.BodeWidthCriterion
