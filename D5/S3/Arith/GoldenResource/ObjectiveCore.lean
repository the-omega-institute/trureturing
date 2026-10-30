/- GID: D5/S3/Arith/GoldenResource/ObjectiveCore
   generality: G
   mirror-B: D5/B/S3/Arith/GoldenResource/ObjectiveCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Divisor resource and prime-local objectives share the exact sigma-ratio identity. -/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.NumberTheory.ArithmeticFunction.Misc

open Finset

namespace D5.S3.Arith.GoldenResourceOptimalInteger

/-- Divisor free energy minus the logarithmic resource cost. -/
noncomputable def goldenResourceObjective (lambda : ℝ) (n : ℕ) : ℝ :=
  Real.log (∑ d ∈ n.divisors, (d : ℝ)⁻¹) - lambda * Real.log n

theorem reciprocal_divisor_sum {n : ℕ} (hn : 1 ≤ n) :
    (∑ d ∈ n.divisors, (d : ℝ)⁻¹) = (ArithmeticFunction.sigma 1 n : ℝ) / n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [ArithmeticFunction.sigma_one_apply, Nat.cast_sum, ← Nat.sum_div_divisors n
    (fun d => (d : ℝ)), sum_div]
  apply sum_congr rfl
  intro d hd
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) hd0]
  field_simp

/-- The resource objective agrees with the divisor-sum ratio expression. -/
theorem golden_resource_sigma_identity (lambda : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    goldenResourceObjective lambda n =
      Real.log ((ArithmeticFunction.sigma 1 n : ℝ) / n) - lambda * Real.log n := by
  rw [goldenResourceObjective, reciprocal_divisor_sum hn]

end D5.S3.Arith.GoldenResourceOptimalInteger

namespace D5.S3.Arith.GoldenLocalThreshold

noncomputable section

/-- The contribution of one prime exponent to the logarithmic objective at price `lambda`. -/
def goldenPrimeLocalObjective (lambda : ℝ) (p a : ℕ) : ℝ :=
  Real.log ((1 - (p : ℝ)⁻¹ ^ (a + 1)) / (1 - (p : ℝ)⁻¹)) -
    lambda * a * Real.log p

end
end D5.S3.Arith.GoldenLocalThreshold
