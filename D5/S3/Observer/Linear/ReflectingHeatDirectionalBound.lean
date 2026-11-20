/- GID: D5/S3/Observer/Linear/ReflectingHeatDirectionalBound
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/ReflectingHeatDirectionalBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Analytic.Entire.DirectionalExponentialType, lake/module/D5.S3.Observer.Linear.ReflectingHeatInterpolation]
   utility: none
   digest: The heat moment interpolant has directional growth at the prescribed half-width. -/

import D5.S3.Analytic.Entire.DirectionalExponentialType
import D5.S3.Observer.Linear.ReflectingHeatInterpolation
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! # Directional growth of the reflecting heat interpolant -/

open Complex MeasureTheory Polynomial
open scoped BigOperators

namespace D5.S3.Observer.Linear.ReflectingHeatInterpolation

open ReflectingHeatStripBound

private theorem norm_omittedPolynomial_radial (n : ℕ) (j : Mode n) (z : ℂ) :
    ‖(omittedPolynomial n j).eval (z * I)‖ ≤ (4 : ℝ) ^ (n - 2) * (1 + ‖z‖) ^ (n - 2) := by
  have hcard : (Finset.univ.erase j).card = n - 2 := by
    simp [Finset.card_erase_of_mem (Finset.mem_univ j), Mode, Nat.sub_sub]
  rw [omittedPolynomial, Lagrange.eval_nodal, norm_prod]
  calc
    _ ≤ ∏ _k ∈ Finset.univ.erase j, (4 * (1 + ‖z‖)) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro k _
      have hq : rate n k ≤ 4 := by unfold rate; linarith [Real.neg_one_le_cos (angle n k)]
      calc
        ‖z * I - (rate n k : ℂ)‖ ≤ ‖z‖ + rate n k := by
          simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (rate_pos n k)]
            using norm_sub_le (z * I) (rate n k : ℂ)
        _ ≤ 4 * (1 + ‖z‖) := by linarith [norm_nonneg z]
    _ = _ := by rw [Finset.prod_const, hcard, mul_pow]

private theorem momentInterpolant_bounded_real (n : ℕ) (j : Mode n) (M : ℂ → ℂ)
    {A B : ℝ} (hA : 0 ≤ A)
    (hM : ∀ ω : ℝ, ∃ ζ : ℂ, ζ ≠ 0 ∧
      ζ + ζ⁻¹ = (ω : ℂ) * I - 2 ∧ 1 ≤ ‖ζ‖ ∧
      ‖M (ω : ℂ)‖ ≤ A * (1 + B * |ω|) / ‖ζ‖ ^ n) :
    ∀ ω : ℝ, ‖momentInterpolant n j M (ω : ℂ)‖ ≤
      (n : ℝ) * A * ((rate n j)⁻¹ + |B|) := by
  intro ω
  obtain ⟨ζ, hζ, hroot, hunit, hbound⟩ := hM ω
  have hn : n - 1 + 1 = n := by have := j.isLt; omega
  let S := Real.sqrt (rate n j ^ 2 + ω ^ 2)
  have hq : 0 < rate n j := rate_pos n j
  have hqS : rate n j ≤ S := by
    dsimp [S]
    calc
      rate n j = Real.sqrt (rate n j ^ 2) := (Real.sqrt_sq hq.le).symm
      _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
  have hωS : |ω| ≤ S := by
    dsimp [S]
    calc
      |ω| = Real.sqrt (ω ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))
  have hS : 0 < S := hq.trans_le hqS
  have hr : 0 < ‖ζ‖ := zero_lt_one.trans_le hunit
  have hpow : ‖ζ‖ ^ n = ‖ζ‖ ^ (n - 1) * ‖ζ‖ := hn ▸ pow_succ ‖ζ‖ (n - 1)
  have haux : ‖M (ω : ℂ)‖ ≤ A * (1 + |B| * |ω|) / ‖ζ‖ ^ n :=
    hbound.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add_right
        (mul_le_mul_of_nonneg_right (le_abs_self B) (abs_nonneg ω)) 1) hA) (by positivity))
  have hratio : (1 + |B| * |ω|) / S ≤ (rate n j)⁻¹ + |B| := by
    rw [add_div, one_div, mul_div_assoc]
    exact add_le_add (inv_anti₀ hq hqS)
      (mul_le_of_le_one_right (abs_nonneg B) ((div_le_one hS).2 hωS))
  rw [momentInterpolant, norm_mul]
  calc
    _ ≤ ((n : ℝ) * ‖ζ‖ ^ (n - 1) / S) *
        (A * (1 + |B| * |ω|) / ‖ζ‖ ^ n) :=
      mul_le_mul (norm_omittedPolynomial_eval n j ω ζ hζ hroot hunit) haux
        (norm_nonneg _) (by positivity)
    _ = (n : ℝ) * A * ((1 + |B| * |ω|) / S) / ‖ζ‖ := by
      rw [hpow]
      field_simp [hS.ne', hr.ne']
      <;> ring
    _ ≤ (n : ℝ) * A * ((1 + |B| * |ω|) / S) :=
      div_le_self (by positivity) hunit
    _ ≤ _ := mul_le_mul_of_nonneg_left hratio (by positivity)

private theorem momentInterpolant_imaginary_node (n : ℕ) (j k : Mode n) (M : ℂ → ℂ) :
    momentInterpolant n j M (-(rate n k : ℂ) * I) =
      if k = j then (nodalDerivative n j : ℂ) * M (-(rate n j : ℂ) * I) else 0 := by
  have harg : (-(rate n k : ℂ) * I) * I = (rate n k : ℂ) := by
    rw [mul_assoc, I_mul_I]
    ring
  rw [momentInterpolant, harg, omittedPolynomial]
  by_cases hk : k = j
  · subst k
    simp only [ite_true, Lagrange.eval_nodal, nodalDerivative, Complex.ofReal_prod,
      Complex.ofReal_sub]
  · have hzero := Lagrange.eval_nodal_at_node (v := fun i : Mode n => (rate n i : ℂ))
      (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩)
    rw [ite_eq_right hk, hzero, zero_mul]

/-- An entire multiplier with the radial half-width bound and the real-axis
envelope gives the contour estimates and the values at the actual moment nodes.
The omitted polynomial contributes exactly n minus two to the bound's order. -/
theorem momentInterpolant_contour_bounds (n : ℕ) (j : Mode n) (M : ℂ → ℂ)
    (hM_entire : Differentiable ℂ M) {L A B C : ℝ} {m : ℕ} (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hM_radial : ∀ z : ℂ, ‖M z‖ ≤ C * (1 + ‖z‖) ^ m * Real.exp (L / 2 * ‖z‖))
    (hM_real : ∀ ω : ℝ, ∃ ζ : ℂ, ζ ≠ 0 ∧
      ζ + ζ⁻¹ = (ω : ℂ) * I - 2 ∧ 1 ≤ ‖ζ‖ ∧
      ‖M (ω : ℂ)‖ ≤ A * (1 + B * |ω|) / ‖ζ‖ ^ n) :
    Differentiable ℂ (momentInterpolant n j M) ∧
    MemLp (fun ω : ℝ => momentInterpolant n j M (ω : ℂ)) 2 volume ∧
    (∫ ω : ℝ, ‖momentInterpolant n j M (ω : ℂ)‖ ^ 2) ≤
      2 * ((n : ℝ) * A) ^ 2 * Real.pi * ((n : ℝ) ^ 2 / 4 + 2 * B ^ 2) ∧
    (∀ z : ℂ, ‖momentInterpolant n j M z‖ ≤
      max ((n : ℝ) * A * ((rate n j)⁻¹ + |B|)) (4 ^ (n - 2) * C) *
        (1 + ‖z‖) ^ (n - 2 + m) * Real.exp (L / 2 * |z.im|)) ∧
    (∀ k : Mode n, momentInterpolant n j M (-(rate n k : ℂ) * I) =
      if k = j then (nodalDerivative n j : ℂ) * M (-(rate n j : ℂ) * I) else 0) := by
  have hF : Differentiable ℂ (momentInterpolant n j M) :=
    (((omittedPolynomial n j).differentiable).comp (differentiable_id.mul_const I)).mul hM_entire
  have hFradial (z : ℂ) : ‖momentInterpolant n j M z‖ ≤
      (4 ^ (n - 2) * C) * (1 + ‖z‖) ^ (n - 2 + m) * Real.exp (L / 2 * ‖z‖) := by
    rw [momentInterpolant, norm_mul]
    calc
      _ ≤ ((4 : ℝ) ^ (n - 2) * (1 + ‖z‖) ^ (n - 2)) *
          (C * (1 + ‖z‖) ^ m * Real.exp (L / 2 * ‖z‖)) :=
        mul_le_mul (norm_omittedPolynomial_radial n j z) (hM_radial z) (norm_nonneg _)
          (by positivity)
      _ = _ := by rw [pow_add]; ring
  obtain ⟨hLp, hnorm⟩ := momentInterpolant_L2_bound n j M
    (hM_entire.continuous.measurable.comp Complex.continuous_ofReal.measurable) hM_real
  exact ⟨hF, hLp, hnorm,
    D5.S3.Analytic.Entire.norm_le_exp_abs_im hF (by positivity)
      (momentInterpolant_bounded_real n j M hA hM_real) hFradial,
    fun k => momentInterpolant_imaginary_node n j k M⟩

end D5.S3.Observer.Linear.ReflectingHeatInterpolation
