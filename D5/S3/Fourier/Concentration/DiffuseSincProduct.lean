/- GID: D5/S3/Fourier/Concentration/DiffuseSincProduct
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/DiffuseSincProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An integrable Euclidean-scale envelope for diffuse finite products of sinc. -/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Pi.Bounds

/-! Quadratic and quartic terms in a product control the diffuse sinc envelope. -/

set_option autoImplicit false

noncomputable section

open Finset
open MeasureTheory
open scoped Interval

namespace D5.S3.Fourier.Concentration.DiffuseSincProduct

private theorem prod_one_add_ge_quadratic {J : Type*} (s : Finset J) (b : J → ℝ)
    (hb : ∀ j ∈ s, 0 ≤ b j) :
    1 + (∑ j ∈ s, b j) + ((∑ j ∈ s, b j) ^ 2 - ∑ j ∈ s, b j ^ 2) / 2 ≤
      ∏ j ∈ s, (1 + b j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hjs ih =>
    have hj : 0 ≤ b j := hb j (mem_insert_self j s)
    have hs (i : J) (hi : i ∈ s) : 0 ≤ b i := hb i (mem_insert_of_mem hi)
    have hcross : 0 ≤ (∑ i ∈ s, b i) ^ 2 - ∑ i ∈ s, b i ^ 2 :=
      sub_nonneg.mpr (sum_sq_le_sq_sum_of_nonneg hs)
    have hextra := mul_nonneg hj hcross
    simp only [sum_insert hjs, prod_insert hjs]
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (ih hs) (by positivity))
    nlinarith

private theorem square_le_prod_one_add {J : Type*} (s : Finset J) (b : J → ℝ)
    (hb : ∀ j ∈ s, 0 ≤ b j) (hd : (∑ j ∈ s, b j ^ 2) ≤ (∑ i ∈ s, b i) ^ 2 / 2) :
    (1 + (∑ j ∈ s, b j) / 2) ^ 2 ≤ ∏ j ∈ s, (1 + b j) := by
  refine le_trans ?_ (prod_one_add_ge_quadratic s b hb)
  nlinarith

private theorem sinc_sq_mul_le_one_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.sinc x ^ 2 * (1 + 2 * x ^ 2 / 15) ≤ 1 := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · simp
  by_cases hsmall : x ≤ 2
  · have hπ : (2 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
    have hc : (1 / 5 : ℝ) ≤ 2 / Real.pi ^ 2 := by
      apply (le_div_iff₀ (by positivity)).2
      have hpi2 := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d2.le 2
      nlinarith
    have hint : (∫ t in (0 : ℝ)..x, Real.cos t) ≤
        ∫ t in (0 : ℝ)..x, (1 - t ^ 2 / 5) := by
      apply intervalIntegral.integral_mono_on hx
        (Real.continuous_cos.intervalIntegrable _ _)
        ((show Continuous (fun t : ℝ => 1 - t ^ 2 / 5) by fun_prop).intervalIntegrable _ _)
      intro t ht
      have htπ : |t| ≤ Real.pi := by
        rw [abs_of_nonneg ht.1]
        exact ht.2.trans (hsmall.trans hπ.le)
      exact (Real.cos_le_one_sub_mul_cos_sq htπ).trans (by
        nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg t)])
    have hpolynomial : (∫ t in (0 : ℝ)..x, (1 - t ^ 2 / 5)) = x - x ^ 3 / 15 := by
      rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
          ((show Continuous (fun t : ℝ => t ^ 2 / 5) by fun_prop).intervalIntegrable _ _),
        intervalIntegral.integral_div, integral_pow]
      simp
      ring
    rw [integral_cos, hpolynomial, Real.sin_zero, sub_zero] at hint
    have hsinc : Real.sinc x ≤ 1 - x ^ 2 / 15 := by
      rw [Real.sinc_of_ne_zero hxpos.ne', div_le_iff₀ hxpos]
      linarith
    have hsinc_nonneg : 0 ≤ Real.sinc x :=
      (Real.sinc_pos (by rw [abs_of_nonneg hx]; exact hsmall.trans_lt hπ)).le
    refine (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hsinc_nonneg hsinc 2)
      (by positivity)).trans ?_
    let a := x ^ 2 / 15
    have hapos : 0 ≤ a := by dsimp [a]; positivity
    have hale : a ≤ 1 := by dsimp [a]; nlinarith [mul_nonneg hx (sub_nonneg.mpr hsmall)]
    have hremain : 0 ≤ a ^ 2 * (3 - 2 * a) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    change (1 - a) ^ 2 * (1 + 2 * x ^ 2 / 15) ≤ 1
    have hfactor : 1 + 2 * x ^ 2 / 15 = 1 + 2 * a := by dsimp [a]; ring
    rw [hfactor]
    nlinarith
  · have hx2 : 2 ≤ x := (lt_of_not_ge hsmall).le
    have hsin : Real.sin x ^ 2 ≤ 1 := by
      simpa using pow_le_pow_left₀ (abs_nonneg (Real.sin x)) (Real.abs_sin_le_one x) 2
    rw [Real.sinc_of_ne_zero hxpos.ne', div_pow, div_mul_eq_mul_div,
      div_le_iff₀ (by positivity)]
    calc
      _ ≤ 1 * (1 + 2 * x ^ 2 / 15) := mul_le_mul_of_nonneg_right hsin (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg hx (sub_nonneg.mpr hx2)]

private theorem sinc_sq_mul_le_one (x : ℝ) :
    Real.sinc x ^ 2 * (1 + 2 * x ^ 2 / 15) ≤ 1 := by
  rcases le_or_gt 0 x with h | h
  · exact sinc_sq_mul_le_one_nonneg h
  · simpa only [Real.sinc_neg, neg_sq] using sinc_sq_mul_le_one_nonneg (neg_nonneg.mpr h.le)

/-- If the fourth powers sum to at most half the squared second moment,
a reciprocal quadratic at the Euclidean scale bounds the finite sinc product. -/
theorem diffuse_sinc_product_le {J : Type*} (s : Finset J) (c : J → ℝ)
    (hc : (∑ j ∈ s, c j ^ 4) ≤ (∑ i ∈ s, c i ^ 2) ^ 2 / 2) (t : ℝ) :
    (∏ j ∈ s, |Real.sinc (c j * t)|) ≤ (1 + (∑ j ∈ s, c j ^ 2) * t ^ 2 / 15)⁻¹ := by
  let b (j : J) := 2 * (c j * t) ^ 2 / 15
  have hb (j : J) : 0 ≤ b j := by dsimp [b]; positivity
  have hsum : (∑ j ∈ s, b j) = (∑ j ∈ s, c j ^ 2) * (2 * t ^ 2 / 15) := by
    rw [sum_mul]
    apply sum_congr rfl
    intro j _
    dsimp [b]
    ring
  have hsum_sq : (∑ j ∈ s, b j ^ 2) =
      (∑ j ∈ s, c j ^ 4) * (2 * t ^ 2 / 15) ^ 2 := by
    rw [sum_mul]
    apply sum_congr rfl
    intro j _
    dsimp [b]
    ring
  have hdiffuse : (∑ j ∈ s, b j ^ 2) ≤ (∑ i ∈ s, b i) ^ 2 / 2 := by
    rw [hsum_sq, hsum, mul_pow]
    linarith [mul_le_mul_of_nonneg_right hc (sq_nonneg (2 * t ^ 2 / 15))]
  have hquad := square_le_prod_one_add s b (fun j _ => hb j) hdiffuse
  have hproduct :
      ∏ j ∈ s, (Real.sinc (c j * t) ^ 2 * (1 + b j)) ≤ 1 := by
    calc
      _ ≤ ∏ _ ∈ s, (1 : ℝ) :=
        prod_le_prod₀ (fun j _ => mul_nonneg (sq_nonneg _)
          (add_nonneg zero_le_one (hb j)))
          (fun j _ => sinc_sq_mul_le_one _)
      _ = _ := prod_const_one
  rw [prod_mul_distrib] at hproduct
  have hsquare :
      (∏ j ∈ s, |Real.sinc (c j * t)|) ^ 2 = ∏ j ∈ s, Real.sinc (c j * t) ^ 2 := by
    rw [← Finset.prod_pow]
    exact prod_congr rfl (fun j _ => sq_abs _)
  let B := 1 + (∑ j ∈ s, b j) / 2
  have hB : 0 < B := by dsimp [B]; linarith [sum_nonneg (fun j _ => hb j) (s := s)]
  have hbound : ((∏ j ∈ s, |Real.sinc (c j * t)|) * B) ^ 2 ≤ 1 := by
    rw [mul_pow, hsquare]
    exact (mul_le_mul_of_nonneg_left hquad (prod_nonneg (fun j _ => sq_nonneg _))).trans hproduct
  have hpos : 0 ≤ (∏ j ∈ s, |Real.sinc (c j * t)|) * B :=
    mul_nonneg (prod_nonneg (fun _ _ => abs_nonneg _)) hB.le
  have hraw : (∏ j ∈ s, |Real.sinc (c j * t)|) ≤ B⁻¹ := by
    rw [← one_div, le_div_iff₀ hB]
    nlinarith
  have hdenom : B = 1 + (∑ j ∈ s, c j ^ 2) * t ^ 2 / 15 := by
    dsimp [B]
    rw [hsum]
    ring
  rwa [hdenom] at hraw

end D5.S3.Fourier.Concentration.DiffuseSincProduct
