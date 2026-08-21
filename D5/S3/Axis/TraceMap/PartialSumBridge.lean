/- GID: D5/S3/Axis/TraceMap/PartialSumBridge
   generality: I
   mirror-B: D5/B/S3/Axis/TraceMap/PartialSumBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The admissible-word sum and the Zeckendorf-range sum agree under one depth shift. -/

import D5.S1.Recurrence.TraceMap
import D5.S3.Axis.AxisPartialSum

namespace D5.S3.Axis.TraceMap.PartialSumBridge

open D5.S1.Recurrence.TraceMap (wordSum admissibleWords wordSum_succ_succ)
open D5.S3.Axis.AxisPartialSum (axisPartialSum wordWeight axisPartialSum_succ_succ)

/- Two formalizations of the same partial sum exist in this repository, written eight days
   apart under different index conventions:

   * `D5/S1/Recurrence/TraceMap.tracePartial`, a sum over `admissibleWords K`, the subsets of
     `range K` with no two adjacent indices, each index `i` weighted at `axisWeight (i + 1)`;
   * `D5/S3/Axis/AxisPartialSum.axisPartialSum`, a sum over `range (fib (K + 1))`, each natural
     weighted by the product of `axisWeight` over its Zeckendorf indices, which start at two.

   They are not interchangeable as written: the depths differ by one and so do the weight
   indices. This module proves the exact relation, so that a statement about one is a statement
   about the other. Both underlying modules are frozen and untouched.

   The proof does not build the Zeckendorf bijection. Both sides already carry the same two
   step recursion as public theorems, and the two base values agree, so induction closes it. -/

/-- Reindexing the weight by one turns the admissible-word sum into the Zeckendorf-range sum
one depth up. -/
theorem wordSum_eq_axisPartialSum (x y : ℝ) :
    ∀ K : ℕ,
      wordSum (fun j => D5.S3.Axis.AxisTraceRecurrence.axisWeight x y (j + 2)) K =
        axisPartialSum x y (K + 1) := by
  intro K
  induction K using Nat.strong_induction_on with
  | _ K ih =>
    match K with
    | 0 =>
      simp [wordSum, admissibleWords, axisPartialSum, wordWeight,
        Nat.zeckendorf_zero, Finset.filter_true_of_mem]
    | 1 =>
      have hg : Nat.greatestFib 1 = 2 := by decide
      have hf : Nat.fib 3 = 2 := by norm_num [Nat.fib]
      have hz1 : Nat.zeckendorf 1 = [2] := by
        rw [Nat.zeckendorf_of_pos Nat.one_pos, hg]
        norm_num [Nat.fib]
      have hset : (({0} : Finset ℕ).powerset.filter
          fun s => ∀ i ∈ s, i + 1 ∉ s) = {∅, {0}} := by decide
      simp [wordSum, admissibleWords, axisPartialSum, wordWeight, hf, hz1, hg,
        Nat.zeckendorf_zero, Finset.sum_range_succ, hset]
    | (n + 2) =>
      have h0 : n < n + 2 := by omega
      have h1 : n + 1 < n + 2 := by omega
      rw [wordSum_succ_succ, ih n h0, ih (n + 1) h1]
      exact (axisPartialSum_succ_succ x y (n + 1)).symm

end D5.S3.Axis.TraceMap.PartialSumBridge
