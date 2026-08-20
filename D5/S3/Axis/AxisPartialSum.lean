/- GID: D5/S3/Axis/AxisPartialSum
   generality: I
   mirror-B: D5/B/S3/Axis/AxisPartialSum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The legal-word partial sum satisfies the two-step trace recurrence. -/

import D5.S3.Axis.AxisTraceRecurrence
import Mathlib.Data.Nat.Fib.Zeckendorf

/- Library-search audit trail (2026-08-19):
   * `Nat.greatestFib_lt : greatestFib m < n ↔ m < fib n` is the exact characterisation of
     digit depth; it turns "legal words of depth at most K" into the initial segment
     `Finset.range (Nat.fib (K + 1))`, so no bespoke word enumeration is introduced.
   * `Nat.zeckendorf_of_pos` supplies the greedy head decomposition and is applied rather
     than reproved; `Nat.fib_add_two` supplies the index arithmetic.
   * `D5.S3.Axis.AxisTraceRecurrence.axisWeight` already carries the weight and its
     multiplicative Fibonacci law; this module adds the partial sum over words.
-/

namespace D5.S3.Axis.AxisPartialSum

open Nat D5.S3.Axis.AxisTraceRecurrence

/-- The weight of one legal word: the product of the axis weights at its occupied digits. -/
noncomputable def wordWeight (x y : ℝ) (n : ℕ) : ℝ :=
  ((Nat.zeckendorf n).map (axisWeight x y)).prod

/-- Depth at most `K` is exactly the initial segment below `fib (K + 1)`. -/
theorem depth_le_iff (n K : ℕ) : Nat.greatestFib n ≤ K ↔ n < Nat.fib (K + 1) := by
  constructor
  · intro h
    exact Nat.greatestFib_lt.mp (Nat.lt_succ_of_le h)
  · intro h
    exact Nat.lt_succ_iff.mp (Nat.greatestFib_lt.mpr h)

/-- The partial sum over all legal words of digit depth at most `K`. -/
noncomputable def axisPartialSum (x y : ℝ) (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (Nat.fib (K + 1)), wordWeight x y n

/-- Adding the next Fibonacci number prepends its index to the word. -/
theorem wordWeight_shift (x y : ℝ) (K m : ℕ) (hm : m < Nat.fib (K + 1)) :
    wordWeight x y (Nat.fib (K + 2) + m) =
      axisWeight x y (K + 2) * wordWeight x y m := by
  have hfib : Nat.fib (K + 3) = Nat.fib (K + 1) + Nat.fib (K + 2) := by
    simpa using Nat.fib_add_two (n := K + 1)
  have hfibpos : 0 < Nat.fib (K + 2) := Nat.fib_pos.mpr (by omega)
  have hpos : 0 < Nat.fib (K + 2) + m := by omega
  have hge : Nat.fib (K + 2) ≤ Nat.fib (K + 2) + m := Nat.le_add_right _ _
  have hlt : Nat.fib (K + 2) + m < Nat.fib (K + 3) := by omega
  have hgreat : Nat.greatestFib (Nat.fib (K + 2) + m) = K + 2 := by
    have hle : K + 2 ≤ Nat.greatestFib (Nat.fib (K + 2) + m) :=
      Nat.le_greatestFib.mpr hge
    have hlt' : Nat.greatestFib (Nat.fib (K + 2) + m) < K + 3 :=
      Nat.greatestFib_lt.mpr hlt
    omega
  have hsub : Nat.fib (K + 2) + m - Nat.fib (K + 2) = m := by omega
  simp only [wordWeight]
  rw [Nat.zeckendorf_of_pos hpos, hgreat, hsub]
  simp [List.map_cons, List.prod_cons]

/-- The two-step trace recurrence: the partial sum at depth `K + 2` splits by its highest
digit, and using digit `K + 2` forces digit `K + 1` to be empty. -/
theorem axisPartialSum_succ_succ (x y : ℝ) (K : ℕ) :
    axisPartialSum x y (K + 2) =
      axisPartialSum x y (K + 1) + axisWeight x y (K + 2) * axisPartialSum x y K := by
  have hfib : Nat.fib (K + 3) = Nat.fib (K + 1) + Nat.fib (K + 2) := by
    simpa using Nat.fib_add_two (n := K + 1)
  have hsplit : Nat.fib (K + 3) = Nat.fib (K + 2) + Nat.fib (K + 1) := by omega
  simp only [axisPartialSum]
  rw [show K + 2 + 1 = K + 3 from rfl, hsplit, Finset.sum_range_add]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro m hm
  exact wordWeight_shift x y K m (Finset.mem_range.mp hm)

#print axioms axisPartialSum_succ_succ

end D5.S3.Axis.AxisPartialSum
