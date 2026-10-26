/- GID: D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveGauss
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveGauss
   mirror-E: none(waiver:coefficient-asymptotics)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Integrals.Basic]
   utility: none
   digest: Sharp upper estimates for the parity-sensitive Gauss coefficient. -/

import D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveReduction
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! A sharp upper bound, retaining the parity constraint, suffices for the D-prime tail. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveGauss

open Finset Real intervalIntegral MeasureTheory
open scoped BigOperators Topology

private theorem quarter_circle_integral (R : ℝ) (hR : 0 ≤ R) :
    (∫ x in 0..R, Real.sqrt (R^2-x^2)) = Real.pi / 4 * R^2 := by
  have hcont : Continuous (fun x : ℝ => Real.sqrt (1-x^2)) := by fun_prop
  have heven : (∫ x in (-1 : ℝ)..0, Real.sqrt (1-x^2)) =
      ∫ x in (0 : ℝ)..1, Real.sqrt (1-x^2) := by
    have h := integral_comp_mul_right (fun x : ℝ => Real.sqrt (1-x^2))
      (a := (-1 : ℝ)) (b := 0) (c := (-1 : ℝ)) (by norm_num)
    simpa only [mul_neg_one, neg_sq, zero_mul, neg_zero, inv_neg, inv_one, neg_one_smul,
      integral_symm (0 : ℝ) 1, neg_neg] using h
  have hquarter : (∫ x in (0 : ℝ)..1, Real.sqrt (1-x^2)) = Real.pi / 4 := by
    have h := integral_add_adjacent_intervals (μ := volume) (hcont.intervalIntegrable (-1) 0)
      (hcont.intervalIntegrable 0 1)
    rw [heven, integral_sqrt_one_sub_sq] at h
    linarith
  have hscale (x : ℝ) : Real.sqrt (R^2-(x*R)^2) = R * Real.sqrt (1-x^2) := by
    rw [show R^2-(x*R)^2 = R^2*(1-x^2) by ring,
      Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq hR]
  have h := smul_integral_comp_mul_right (fun x : ℝ => Real.sqrt (R^2-x^2))
    (a := (0 : ℝ)) (b := 1) R
  simp only [zero_mul, one_mul, smul_eq_mul, hscale, intervalIntegral.integral_const_mul, hquarter] at h
  rw [← h]
  ring

private theorem sqrt_row_sum_le (R : ℝ) (hR : 0 ≤ R) (r : ℕ) :
    (∑ a ∈ range r, Real.sqrt (R^2-((a : ℝ)+1/2)^2)) ≤
      Real.pi / 4 * R^2 + R := by
  let f : ℝ → ℝ := fun x => Real.sqrt (R^2-x^2)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hanti : AntitoneOn f (Set.Ici 0) := by
    intro x hx y hy hxy
    simp only [Set.mem_Ici] at hx hy
    dsimp [f]
    apply Real.sqrt_le_sqrt
    nlinarith
  have hs := (hanti.mono (show Set.Icc (0 : ℝ) (0 + r) ⊆ Set.Ici 0 from fun x hx => hx.1)).sum_le_integral
  simp only [zero_add] at hs
  have hshift := sum_range_succ' (fun a : ℕ => f a) r
  rw [sum_range_succ] at hshift
  simp only [Nat.cast_zero] at hshift
  have hi : (∫ x in 0..(r : ℝ), f x) ≤ ∫ x in 0..R, f x := by
    by_cases hr : (r : ℝ) ≤ R
    · apply integral_mono_interval le_rfl (Nat.cast_nonneg r) hr
      · exact ae_of_all _ fun x => Real.sqrt_nonneg _
      · exact hf.intervalIntegrable _ _
    · have hzero : (∫ x in R..(r : ℝ), f x) = 0 := by
        apply integral_zero_ae
        apply ae_of_all
        intro x hx
        rw [Set.uIoc_of_le (le_of_not_ge hr)] at hx
        dsimp [f]
        apply Real.sqrt_eq_zero_of_nonpos
        nlinarith [hx.1, hx.2]
      have h := integral_add_adjacent_intervals (μ := volume) (hf.intervalIntegrable 0 R)
        (hf.intervalIntegrable R r)
      rw [hzero, add_zero] at h
      exact le_of_eq h.symm
  have hsum : (∑ a ∈ range r, f a) ≤ (∫ x in 0..R, f x) + f 0 := by
    have hnon : 0 ≤ f r := Real.sqrt_nonneg _
    linarith
  calc
    _ ≤ ∑ a ∈ range r, f a := by
      apply sum_le_sum
      intro a _
      apply hanti
      · change (0 : ℝ) ≤ (a : ℝ); positivity
      · change (0 : ℝ) ≤ (a : ℝ)+1/2; positivity
      · linarith
    _ ≤ (∫ x in 0..R, f x) + f 0 := hsum
    _ = _ := by rw [quarter_circle_integral R hR]; simp [f, Real.sqrt_sq hR]

/-- The parity-compatible Gauss count has leading upper constant `π/4`, along all indices. -/
theorem gauss_coefficient_upper (n : ℕ) :
    ((PowerSeries.coeff n
      (AndrewsElBachraouiFiveReduction.productTrunc 2 n) : ℤ) : ℝ) ≤
      Real.pi / 4 * n + 5 / 4 * Real.sqrt (2 * (n : ℝ) + 1 / 2) +
        Real.pi / 16 + 3 / 8 := by
  classical
  let s := ((range (n+1)) ×ˢ range (n+1)).filter (fun p : ℕ × ℕ =>
    (p.1+1).choose 2 + (p.2+1).choose 2 ≤ n ∧
      ((p.1+1).choose 2 + (p.2+1).choose 2) % 2 = n % 2)
  have hc := (AndrewsElBachraouiBounds.gauss_product_coefficient_count_bound n).1
  have hb := AndrewsElBachraouiBounds.gauss_pair_count_le_sqrt_sum n s
    (fun p hp => (mem_filter.mp hp).2)
  change (PowerSeries.coeff n (AndrewsElBachraouiFiveReduction.productTrunc 2 n) : ℤ) = s.card at hc
  rw [hc]
  let R := Real.sqrt (2 * (n : ℝ) + 1/2)
  let r : ℕ := ⌊R+1/2⌋₊
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R^2 = 2*(n : ℝ)+1/2 := Real.sq_sqrt (by positivity)
  have hr : (r : ℝ) ≤ R+1/2 := Nat.floor_le (by positivity)
  have hs := sqrt_row_sum_le R hR r
  have hsum : (∑ a ∈ range r, (Real.sqrt (R^2-((a : ℝ)+1/2)^2)/2+3/4)) =
      (∑ a ∈ range r, Real.sqrt (R^2-((a : ℝ)+1/2)^2))/2 + 3/4*r := by
    simp [sum_add_distrib, div_eq_mul_inv, sum_mul]; ring
  change (s.card : ℝ) ≤ ∑ a ∈ range r, _ at hb
  rw [hsum] at hb
  change (s.card : ℝ) ≤ _
  change (s.card : ℝ) ≤ Real.pi/4*n+5/4*R+Real.pi/16+3/8
  nlinarith

end D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveGauss
