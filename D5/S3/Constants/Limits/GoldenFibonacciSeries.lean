/- GID: D5/S3/Constants/Limits/GoldenFibonacciSeries
   generality: I
   mirror-B: D5/B/S3/Constants/Limits/GoldenFibonacciSeries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Sum the alternating golden Fibonacci scale exactly. -/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Real.GoldenRatio

namespace D5.S3.Constants.Limits.GoldenFibonacciSeries

open Real

/-- The golden-conjugate weighting of the shifted Fibonacci scale sums to
half the reciprocal golden ratio. -/
theorem golden_fibonacci_series_has_sum :
    HasSum
      (fun k : Nat =>
        goldenConj ^ k * (Nat.fib (k + 1) : Real) / goldenRatio ^ (k + 2))
      (1 / (2 * goldenRatio)) := by
  let x : Real := goldenConj / goldenRatio
  have hphi_ne : goldenRatio ≠ 0 := goldenRatio_ne_zero
  have hsqrt_ne : Real.sqrt 5 ≠ 0 := by positivity
  have hpsi_abs : |goldenConj| < 1 := by
    rw [abs_of_neg goldenConj_neg]
    linarith [neg_one_lt_goldenConj]
  have hx_abs : |x| < 1 := by
    rw [abs_div, abs_of_neg goldenConj_neg, abs_of_pos goldenRatio_pos]
    exact (div_lt_one goldenRatio_pos).2 (by
      linarith [neg_one_lt_goldenConj, one_lt_goldenRatio])
  have hphi_x_abs : |goldenRatio * x| < 1 := by
    have hphi_x : goldenRatio * x = goldenConj := by
      dsimp [x]
      field_simp
    rwa [hphi_x]
  have hpsi_x_abs : |goldenConj * x| < 1 := by
    rw [abs_mul]
    calc
      |goldenConj| * |x| < 1 * |x| :=
        mul_lt_mul_of_pos_right hpsi_abs
          (abs_pos.mpr (div_ne_zero goldenConj_ne_zero hphi_ne))
      _ < 1 * 1 := mul_lt_mul_of_pos_left hx_abs zero_lt_one
      _ = 1 := one_mul 1
  have hgenerating :
      HasSum (fun k : Nat => (Nat.fib (k + 1) : Real) * x ^ k)
        ((goldenRatio / Real.sqrt 5) * (1 - goldenRatio * x)⁻¹ -
          (goldenConj / Real.sqrt 5) * (1 - goldenConj * x)⁻¹) := by
    have hphi :=
      (hasSum_geometric_of_abs_lt_one hphi_x_abs).mul_left
        (goldenRatio / Real.sqrt 5)
    have hpsi :=
      (hasSum_geometric_of_abs_lt_one hpsi_x_abs).mul_left
        (goldenConj / Real.sqrt 5)
    refine HasSum.congr_fun (hphi.sub hpsi) fun k => ?_
    rw [Real.coe_fib_eq, mul_pow, mul_pow]
    ring
  have hphi_x : goldenRatio * x = goldenConj := by
    dsimp [x]
    field_simp
  have hpsi_x : goldenConj * x = 1 / goldenRatio ^ 3 := by
    have hpsi_eq : goldenConj = -goldenRatio⁻¹ := by
      linarith [inv_goldenRatio]
    change goldenConj * (goldenConj / goldenRatio) = 1 / goldenRatio ^ 3
    rw [hpsi_eq]
    simp only [div_eq_mul_inv, pow_succ, mul_inv_rev]
    ring
  have hsecond_denominator :
      1 - goldenConj * x = 2 / goldenRatio ^ 2 := by
    rw [hpsi_x]
    have hinv : goldenRatio⁻¹ = goldenRatio - 1 := by
      linarith [inv_goldenRatio, goldenRatio_add_goldenConj]
    rw [one_div, ← inv_pow, div_eq_mul_inv, ← inv_pow, hinv]
    nlinarith [goldenRatio_sq]
  have hgenerating_value :
      (goldenRatio / Real.sqrt 5) * (1 - goldenRatio * x)⁻¹ -
          (goldenConj / Real.sqrt 5) * (1 - goldenConj * x)⁻¹ =
        goldenRatio / 2 := by
    rw [hphi_x, one_sub_goldenRatio, hsecond_denominator]
    have hfirst :
        (goldenRatio / Real.sqrt 5) * goldenRatio⁻¹ = 1 / Real.sqrt 5 := by
      field_simp [hphi_ne, hsqrt_ne]
    have hsecond : (2 / goldenRatio ^ 2)⁻¹ = goldenRatio ^ 2 / 2 := by
      field_simp [hphi_ne]
    rw [hfirst, hsecond, ← goldenRatio_sub_goldenConj]
    have hdiff_ne : goldenRatio - goldenConj ≠ 0 := by
      rw [goldenRatio_sub_goldenConj]
      exact hsqrt_ne
    calc
      1 / (goldenRatio - goldenConj) -
            goldenConj / (goldenRatio - goldenConj) * (goldenRatio ^ 2 / 2) =
          (1 - goldenConj * (goldenRatio ^ 2 / 2)) /
            (goldenRatio - goldenConj) := by ring
      _ = goldenRatio / 2 := by
        apply (div_eq_iff hdiff_ne).2
        nlinarith [goldenRatio_sq, goldenRatio_mul_goldenConj]
  have hscaled := hgenerating.mul_left (1 / goldenRatio ^ 2)
  rw [hgenerating_value] at hscaled
  have term_scale (a b c : Real) (k : Nat) :
      b ^ k * c / a ^ (k + 2) = 1 / a ^ 2 * (c * (b / a) ^ k) := by
    rw [div_pow, pow_add]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hterms :
      HasSum
        (fun k : Nat =>
          goldenConj ^ k * (Nat.fib (k + 1) : Real) / goldenRatio ^ (k + 2))
        (1 / goldenRatio ^ 2 * (goldenRatio / 2)) := by
    refine HasSum.congr_fun hscaled fun k => ?_
    change goldenConj ^ k * (Nat.fib (k + 1) : Real) / goldenRatio ^ (k + 2) =
      1 / goldenRatio ^ 2 *
        ((Nat.fib (k + 1) : Real) * (goldenConj / goldenRatio) ^ k)
    exact term_scale goldenRatio goldenConj (Nat.fib (k + 1) : Real) k
  have hvalue :
      1 / goldenRatio ^ 2 * (goldenRatio / 2) = 1 / (2 * goldenRatio) := by
    field_simp [hphi_ne]
  rwa [hvalue] at hterms

end D5.S3.Constants.Limits.GoldenFibonacciSeries
