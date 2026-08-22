/- GID: D5/S3/Axis/AxisTraceDefinitions
   generality: I
   mirror-B: D5/B/S3/Axis/AxisTraceDefinitions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The partial sum ranges over words of bounded depth; the weight is the exponential. -/

import D5.S3.Axis.AxisPartialSum

namespace D5.S3.Axis.AxisTraceDefinitions

open Real
open D5.S3.Axis.AxisTraceRecurrence
open D5.S3.Axis.AxisPartialSum

/-- The two objects the clause introduces, pinned to their definitions, together with the
bridge that makes the first one mean what the source says it means.

The source writes the partial sum as a sum over legal words of digit depth at most `K`.
The implementation sums over an initial segment of the naturals instead, which is the same
family only because depth at most `K` is exactly membership below the next Fibonacci number.
Without that bridge the range in the definition would be an unexplained constant. -/
theorem axis_trace_definitions (x y : ℝ) :
    (∀ K : ℕ, axisWeight x y K = Real.exp (-x * goldenRatio ^ (K + 1) +
        y * goldenConj ^ (K + 1))) ∧
      (∀ K : ℕ, axisPartialSum x y K =
          ∑ n ∈ Finset.range (Nat.fib (K + 1)), wordWeight x y n) ∧
        ∀ n K : ℕ, Nat.greatestFib n ≤ K ↔ n < Nat.fib (K + 1) :=
  ⟨fun _ => rfl, fun _ => rfl, depth_le_iff⟩

end D5.S3.Axis.AxisTraceDefinitions
