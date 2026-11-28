/- GID: D5/S3/Weil/Analytic/MobiusDiscreteAbel
   generality: I
   mirror-B: none(waiver:mobius-log-fourth-support)
   mirror-E: none(waiver:mobius-log-fourth)
   anchors: []
   utility: none
   digest: Discrete Abel summation expresses a logarithm-weighted Möbius prefix. -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-! Finite Abel summation for the logarithm-weighted Möbius coefficients. -/

set_option autoImplicit false

open Finset
open scoped ArithmeticFunction.Moebius

namespace MobiusDiscreteAbel

private theorem sum_Ioc_succ (f : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Ioc 0 (n + 1), f j) = (∑ j ∈ Ioc 0 n, f j) + f (n + 1) := by
  rw [← Ioc_union_Ioc_eq_Ioc (Nat.zero_le n) (Nat.le_succ n),
    Finset.sum_union (Ioc_disjoint_Ioc_of_le le_rfl),
    Nat.Ioc_succ_singleton, Finset.sum_singleton]

/-- The finite correction uses only values of the Möbius prefix strictly below the endpoint. -/
theorem log_weight_eq_prefix_sub (N : ℕ) :
    (∑ n ∈ Ioc 0 (N + 1), (μ n : ℝ) * Real.log (n : ℝ)) =
      (∑ n ∈ Ioc 0 (N + 1), (μ n : ℝ)) * Real.log ((N + 1 : ℕ) : ℝ) -
      ∑ m ∈ Ioc 0 N, (∑ n ∈ Ioc 0 m, (μ n : ℝ)) *
        (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) := by
  induction N with
  | zero => simp [Nat.Ioc_succ_singleton]
  | succ N ih =>
    rw [sum_Ioc_succ (fun n => (μ n : ℝ) * Real.log (n : ℝ)) (N + 1), ih,
      sum_Ioc_succ (fun n => (μ n : ℝ)) (N + 1),
      sum_Ioc_succ (fun m => (∑ n ∈ Ioc 0 m, (μ n : ℝ)) *
        (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ))) N]
    ring

theorem log_increment_le_reciprocal {m : ℕ} (hm : 0 < m) :
    Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) ≤ (m : ℝ)⁻¹ := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hnext : 0 < (m : ℝ) + 1 := by positivity
  push_cast
  rw [← Real.log_div hnext.ne' hm'.ne']
  calc
    _ ≤ ((m : ℝ) + 1) / m - 1 := Real.log_le_sub_one_of_pos (div_pos hnext hm')
    _ = (m : ℝ)⁻¹ := by
      field_simp
      ring

end MobiusDiscreteAbel
