/- GID: D5/S0/Naming/Composition/ConnectionCoefficientComposition
   generality: G
   mirror-B: D5/B/S0/Naming/Composition/ConnectionCoefficientComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Connection coefficients multiply along a two-step completion path. -/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace D5.S0.Naming.Composition.ConnectionCoefficientComposition

theorem connection_coefficient_multiplication :
    (∀ (a b X Y Z : ℝ),
      Y = a * X → Z = b * Y → Z = (a * b) * X) ∧
    (∀ (x : ℝ), 0 < x →
      Real.sqrt (Real.pi * Real.exp x / (2 * x)) =
        Real.sqrt (Real.pi / 2) * Real.exp (x / 2) * x ^ (-1 / 2 : ℝ)) := by
  constructor
  · intro a b X Y Z hY hZ
    calc
      Z = b * Y := hZ
      _ = b * (a * X) := by rw [hY]
      _ = (a * b) * X := by
        simpa [smul_eq_mul, mul_comm] using (SemigroupAction.mul_smul b a X).symm
  · intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hrad : 0 ≤ Real.pi * Real.exp x / (2 * x) := by
      positivity
    have hpi : (Real.sqrt (Real.pi / 2)) ^ 2 = Real.pi / 2 := by
      exact Real.sq_sqrt (by positivity)
    have hexp : (Real.exp (x / 2)) ^ 2 = Real.exp x := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hrpow : (x ^ (-1 / 2 : ℝ)) ^ 2 = x⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hx)]
      norm_num
      exact Real.rpow_neg_one x
    have hproduct :
        (Real.sqrt (Real.pi / 2) * Real.exp (x / 2) * x ^ (-1 / 2 : ℝ)) ^ 2 =
          Real.pi * Real.exp x / (2 * x) := by
      rw [mul_pow, mul_pow, hpi, hexp, hrpow]
      field_simp [hx0]
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    calc
      (Real.sqrt (Real.pi * Real.exp x / (2 * x))) ^ 2 =
          Real.pi * Real.exp x / (2 * x) := Real.sq_sqrt hrad
      _ = (Real.sqrt (Real.pi / 2) * Real.exp (x / 2) *
          x ^ (-1 / 2 : ℝ)) ^ 2 := hproduct.symm

-- Reverse probe for the first public conjunct: both equations are needed.
example :
    (6 : ℝ) = (2 * 3) * 1 := by
  exact connection_coefficient_multiplication.1 2 3 1 2 6 (by norm_num) (by norm_num)

-- Reverse probe for the analytic conjunct at the source's positive point x = 1.
example :
    Real.sqrt (Real.pi * Real.exp (1 : ℝ) / (2 * 1)) =
      Real.sqrt (Real.pi / 2) * Real.exp ((1 : ℝ) / 2) *
        (1 : ℝ) ^ (-1 / 2 : ℝ) := by
  exact connection_coefficient_multiplication.2 1 (by norm_num)

end D5.S0.Naming.Composition.ConnectionCoefficientComposition
