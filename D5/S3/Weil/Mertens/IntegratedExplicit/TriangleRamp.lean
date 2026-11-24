/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/TriangleRamp
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/TriangleRamp
   mirror-E: none(waiver:direct-analytic-kernel)
   anchors: []
   utility: none
   digest: Integral removal of an affine ramp produces the triangular weight. -/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Mul
import Mathlib.Tactic

/-! The running-average operator changes affine positive parts into triangular weights. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRamp

/-- Remove twice the running average, with the lower endpoint fixed at one. -/
def removeAverage (f : ℝ → ℝ) (x : ℝ) : ℝ := f x - 2 / x * ∫ t in 1..x, f t

/-- A ramp whose value is zero at its entry point. -/
def ramp (n t : ℝ) : ℝ := max (t / n - 1) 0

private lemma ramp_integral {n x : ℝ} (hn : 1 ≤ n) (hnx : n ≤ x) :
    (∫ t in 1..x, ramp n t) = (x - n) ^ 2 / (2 * n) := by
  have hn0 : 0 < n := by linarith
  have hc : Continuous (ramp n) := by unfold ramp; fun_prop
  have hz : (∫ t in (1 : ℝ)..n, ramp n t) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards with t ht
    rw [uIoc_of_le hn] at ht
    exact max_eq_right (by
      have := (div_le_one hn0).mpr ht.2
      linarith)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 1 n) (hc.intervalIntegrable n x), hz, zero_add]
  have he : (∫ t in n..x, ramp n t) = ∫ t in n..x, (t / n - 1) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hnx] at ht
    exact max_eq_left (by
      have := (one_le_div hn0).mpr ht.1
      linarith)
  rw [he, intervalIntegral.integral_sub
    ((by fun_prop : Continuous (fun t : ℝ => t / n)).intervalIntegrable n x)
    (continuous_const.intervalIntegrable n x),
    intervalIntegral.integral_div, integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul, mul_one]
  field_simp
  ; ring

/-- The exact kernel change, including both sides of the entry point. -/
theorem removeAverage_ramp {n x : ℝ} (hn : 1 ≤ n) (hx : 0 < x) :
    removeAverage (ramp n) x = max (1 - n / x) 0 := by
  have hn0 : 0 < n := by linarith
  have hx0 : 0 < x := hx
  by_cases hnx : n ≤ x
  · rw [removeAverage, ramp_integral hn hnx, ramp,
      max_eq_left (by have := (one_le_div hn0).mpr hnx; linarith),
      max_eq_left (by have := (div_le_one hx0).mpr hnx; linarith)]
    field_simp
    ; ring
  · have hxn : x ≤ n := (lt_of_not_ge hnx).le
    have hz : ∫ t in (1 : ℝ)..x, ramp n t = 0 := by
      apply intervalIntegral.integral_zero_ae
      filter_upwards with t ht
      exact max_eq_right (by
        have := (div_le_one hn0).mpr (ht.2.trans (max_le hn hxn))
        linarith)
    rw [removeAverage, hz, mul_zero, sub_zero, ramp,
      max_eq_right (by have := (div_le_one hn0).mpr hxn; linarith),
      max_eq_right (by have := (one_le_div hx0).mpr hxn; linarith)]

private lemma sqrt_integral {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in (1 : ℝ)..x, Real.sqrt t) = 2 / 3 * (x * Real.sqrt x - 1) := by
  have hx0 : 0 < x := by linarith
  simp_rw [Real.sqrt_eq_rpow]
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 1 / 2))]
  rw [show (1 / 2 : ℝ) + 1 = 1 + 1 / 2 by ring,
    Real.rpow_add hx0, Real.rpow_one]
  norm_num
  ring

/-- The loss in the square-root envelope retains the exact lower-endpoint term. -/
theorem removeAverage_sqrt_bound {f : ℝ → ℝ} {C x : ℝ} (hx : 1 ≤ x)
    (hend : |f x| ≤ C * Real.sqrt x)
    (hbound : ∀ᵐ t : ℝ, t ∈ Ioc 1 x → |f t| ≤ C * Real.sqrt t) :
    |removeAverage f x| ≤ 7 * C / 3 * Real.sqrt x - 4 * C / (3 * x) := by
  have hx0 : 0 < x := by linarith
  have hi : |∫ t in (1 : ℝ)..x, f t| ≤
      C * (2 / 3 * (x * Real.sqrt x - 1)) := by
    calc
      _ ≤ ∫ t in (1 : ℝ)..x, C * Real.sqrt t :=
        (by
          simpa only [Real.norm_eq_abs] using
            intervalIntegral.norm_integral_le_of_norm_le
              (f := f) (g := fun t => C * Real.sqrt t) (μ := volume) hx
              (hbound.mono (fun t ht htx => by
                simpa only [Real.norm_eq_abs] using ht htx))
              ((continuous_const.mul Real.continuous_sqrt).intervalIntegrable 1 x))
      _ = _ := by rw [intervalIntegral.integral_const_mul, sqrt_integral hx]
  calc
    |removeAverage f x| ≤ |f x| + |2 / x * ∫ t in (1 : ℝ)..x, f t| :=
      abs_sub _ _
    _ = |f x| + (2 / x) * |∫ t in (1 : ℝ)..x, f t| := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) / x)]
    _ ≤ C * Real.sqrt x + (2 / x) *
        (C * (2 / 3 * (x * Real.sqrt x - 1))) := by
      gcongr
    _ = _ := by field_simp; ring

/-- The main-term transform has an exact boundary correction for arbitrary a. -/
theorem removeAverage_main (a : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    removeAverage (fun t => t * Real.log t - a * t) x =
      x / 2 - (a + 1 / 2) / x := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · simp [removeAverage]
  have hx0 : 0 < x := hx
  let F (t : ℝ) := t ^ 2 / 2 * Real.log t - t ^ 2 / 4 - a * t ^ 2 / 2
  have hpos (t : ℝ) (ht : t ∈ uIcc 1 x) : 0 < t :=
    lt_of_lt_of_le (lt_min zero_lt_one hx) ht.1
  have hi : IntervalIntegrable (fun t => t * Real.log t - a * t) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    exact (continuousOn_id.mul
      (Real.continuousOn_log.mono (fun t ht => ne_of_gt (hpos t ht)))).sub
      (continuous_const.mul continuous_id).continuousOn
  have hd (t : ℝ) (ht : t ∈ uIcc 1 x) :
      HasDerivAt F (t * Real.log t - a * t) t := by
    have ht0 : t ≠ 0 := ne_of_gt (hpos t ht)
    convert ((((hasDerivAt_id t).pow 2).div_const 2).mul
      (Real.hasDerivAt_log ht0)).sub (((hasDerivAt_id t).pow 2).div_const 4) |>.sub
      ((((hasDerivAt_id t).pow 2).const_mul a).div_const 2) using 1
    · funext u
      simp only [F, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
    · simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
      field_simp
      ; ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [removeAverage, he]
  simp only [F, Real.log_one, mul_zero, one_pow]
  field_simp
  ; ring

/-- Endpoint minima for the concave error between a triangular affine sum and its main term. -/
theorem affine_sqrt_ge_endpoints {A B a b x : ℝ} (hB : 0 ≤ B)
    (ha : 0 < a) (hx : x ∈ Icc a b) :
    min (A - B / a - a / 2 + Real.sqrt a)
      (A - B / b - b / 2 + Real.sqrt b) ≤ A - B / x - x / 2 + Real.sqrt x := by
  have hinv : ConvexOn ℝ (Ioi 0) (fun t : ℝ => t⁻¹) := by
    simpa using (convexOn_zpow (-1 : ℤ) :
      ConvexOn ℝ (Ioi 0) (fun t : ℝ => t ^ (-1 : ℤ)))
  have hdiv : ConvexOn ℝ (Ioi 0) (fun t : ℝ => B / t) := by
    simpa only [smul_eq_mul, div_eq_mul_inv] using ConvexOn.smul hB hinv
  have hlin : ConvexOn ℝ (Ioi 0) (fun t : ℝ => t / 2) := by
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm, id_eq, one_mul] using
      ConvexOn.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (convexOn_id (convex_Ioi (0 : ℝ)))
  have hsqrt : ConcaveOn ℝ (Ioi 0) Real.sqrt :=
    Real.strictConcaveOn_sqrt.concaveOn.subset Ioi_subset_Ici_self (convex_Ioi 0)
  have hc : ConcaveOn ℝ (Ioi 0)
      (fun t : ℝ => A - B / t - t / 2 + Real.sqrt t) :=
    (((concaveOn_const (c := A) (convex_Ioi 0)).sub hdiv).sub hlin).add hsqrt
  exact hc.ge_on_segment ha (lt_of_lt_of_le ha (hx.1.trans hx.2)) (Icc_subset_segment hx)

end D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRamp
