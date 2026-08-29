/- GID: D5/S3/ObserverMemory/Trajectories/FibonacciNearReturn
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Trajectories/FibonacciNearReturn
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fibonacci times return the golden circle rotation with alternating defect. -/

/- Library-search audit trail (2026-08-29):
   * Exact local hit: `D5.S1.Scale.fibonacci_golden_residual` gives the
     consecutive-Fibonacci residual used to compute the return defect.
   * Pinned Mathlib supplies `add_right_iterate_apply`,
     `AddCircle.coe_eq_zero_iff`, `tendsto_add_atTop_iff_nat`,
     `tendsto_pow_atTop_nhds_zero_of_abs_lt_one`, and the `SignType` lemmas.
   * Searches for the inverse-golden rotation, its Fibonacci return defect,
     and a theorem combining the exact return, decay, and alternating sign
     found no exact declaration in D5 or pinned Mathlib.
-/

import D5.S1.Scale.FibonacciErrorRatio
import Mathlib.Topology.Instances.AddCircle.Defs

namespace D5.S3.ObserverMemory.Trajectories.FibonacciNearReturn

open Filter Topology

/-- Rotation of the unit additive circle by the reciprocal golden ratio. -/
noncomputable def goldenRotation (x : AddCircle (1 : Real)) : AddCircle (1 : Real) :=
  x + ((1 / Real.goldenRatio : Real) : AddCircle (1 : Real))

/-- The real lift left after removing the preceding integer Fibonacci turn. -/
noncomputable def fibonacciReturnDefect (n : Nat) : Real :=
  (Nat.fib n : Real) / Real.goldenRatio - Nat.fib (n - 1)

private theorem fibonacci_return_defect_aux (n : Nat) (hn : 1 ≤ n) :
    fibonacciReturnDefect n =
      (-1 / Real.goldenRatio) ^ (n - 1) / Real.goldenRatio := by
  have hphi : Real.goldenRatio ≠ 0 := Real.goldenRatio_pos.ne'
  have hres := D5.S1.Scale.fibonacci_golden_residual (n - 1)
  have hn_eq : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [hn_eq] at hres
  rw [fibonacciReturnDefect]
  calc
    (Nat.fib n : Real) / Real.goldenRatio - Nat.fib (n - 1) =
        ((Nat.fib n : Real) - Nat.fib (n - 1) * Real.goldenRatio) /
          Real.goldenRatio := by field_simp
    _ = (-1 / Real.goldenRatio) ^ (n - 1) / Real.goldenRatio := by
      congr 1
      linarith

private theorem fibonacci_return_defect_exact (n : Nat) (hn : 1 ≤ n) :
    fibonacciReturnDefect n =
      (-1 : Real) ^ (n - 1) * Real.goldenRatio ^ (-(n : Int)) := by
  rw [fibonacci_return_defect_aux n hn, div_pow]
  rw [show (-(n : Int)) = -((n - 1 : Nat) : Int) - 1 by omega]
  rw [zpow_sub₀ Real.goldenRatio_pos.ne', zpow_neg, zpow_natCast, zpow_one]
  ring

private theorem golden_rotation_iterate (m : Nat) (x : AddCircle (1 : Real)) :
    (goldenRotation^[m]) x =
      x + ((m * (1 / Real.goldenRatio) : Real) : AddCircle (1 : Real)) := by
  change (((· + ((1 / Real.goldenRatio : Real) : AddCircle (1 : Real)))^[m]) x) = _
  rw [add_right_iterate_apply, ← AddCircle.coe_nsmul]
  congr 1
  simp [nsmul_eq_mul]

private theorem golden_rotation_fibonacci_return
    (n : Nat) (x : AddCircle (1 : Real)) :
    (goldenRotation^[Nat.fib n]) x =
      x + ((fibonacciReturnDefect n : Real) : AddCircle (1 : Real)) := by
  rw [golden_rotation_iterate]
  congr 1
  have hinteger :
      (((Nat.fib (n - 1) : Real) : Real) : AddCircle (1 : Real)) = 0 := by
    apply (AddCircle.coe_eq_zero_iff (1 : Real)).mpr
    refine ⟨(Nat.fib (n - 1) : Int), ?_⟩
    simp
  rw [fibonacciReturnDefect, AddCircle.coe_sub, hinteger, sub_zero]
  congr 1
  simp [div_eq_mul_inv]

private theorem fibonacci_return_defect_abs (n : Nat) (hn : 1 ≤ n) :
    |fibonacciReturnDefect n| = Real.goldenRatio ^ (-(n : Int)) := by
  rw [fibonacci_return_defect_exact n hn, abs_mul, abs_pow, abs_neg, abs_one,
    abs_zpow, abs_of_pos Real.goldenRatio_pos]
  simp

private theorem fibonacci_return_defect_tendsto :
    Tendsto (fun n : Nat => |fibonacciReturnDefect n|) atTop (nhds 0) := by
  have hbase : |1 / Real.goldenRatio| < 1 := by
    rw [abs_div, abs_one, abs_of_pos Real.goldenRatio_pos]
    exact (div_lt_one Real.goldenRatio_pos).mpr Real.one_lt_goldenRatio
  have hpow := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hbase
  have hscaled := hpow.div_const Real.goldenRatio
  have hshifted :
      Tendsto (fun n : Nat => |fibonacciReturnDefect (n + 1)|) atTop (nhds 0) := by
    convert hscaled using 1
    · ext n
      rw [fibonacci_return_defect_aux (n + 1) (by omega), Nat.add_sub_cancel,
        abs_div, abs_pow, abs_div, abs_neg, abs_one,
        abs_of_pos Real.goldenRatio_pos]
    · simp
  exact (tendsto_add_atTop_iff_nat 1).mp hshifted

private theorem fibonacci_return_defect_sign (n : Nat) (hn : 1 ≤ n) :
    SignType.sign (fibonacciReturnDefect n) = (-1 : SignType) ^ (n - 1) := by
  rw [fibonacci_return_defect_exact n hn, sign_mul, sign_pow,
    sign_neg (by norm_num : (-1 : Real) < 0)]
  rw [sign_pos (zpow_pos Real.goldenRatio_pos _)]
  simp

/-- Fibonacci return times have the exact alternating inverse-golden defect,
whose magnitude decays to zero while its sign alternates. -/
theorem fibonacci_near_return :
    (∀ n : Nat, ∀ x : AddCircle (1 : Real),
      (goldenRotation^[Nat.fib n]) x =
        x + ((fibonacciReturnDefect n : Real) : AddCircle (1 : Real))) ∧
    (∀ n : Nat, 1 ≤ n →
      fibonacciReturnDefect n =
        (-1 : Real) ^ (n - 1) * Real.goldenRatio ^ (-(n : Int))) ∧
    (∀ n : Nat, 1 ≤ n →
      |fibonacciReturnDefect n| = Real.goldenRatio ^ (-(n : Int))) ∧
    Tendsto (fun n : Nat => |fibonacciReturnDefect n|) atTop (nhds 0) ∧
    (∀ n : Nat, 1 ≤ n →
      SignType.sign (fibonacciReturnDefect n) = (-1 : SignType) ^ (n - 1)) := by
  exact ⟨golden_rotation_fibonacci_return,
    fibonacci_return_defect_exact, fibonacci_return_defect_abs,
    fibonacci_return_defect_tendsto, fibonacci_return_defect_sign⟩

end D5.S3.ObserverMemory.Trajectories.FibonacciNearReturn
