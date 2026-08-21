/- GID: D5/S3/Axis/TraceMap/Theorem635
   generality: I
   mirror-B: D5/B/S3/Axis/TraceMap/Theorem635
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The three clauses of the axis trace map theorem hold of one pair of sequences. -/

import D5.S3.Axis.AxisTraceDefinitions
import D5.S3.Axis.AxisRecurrencePair
import D5.S3.Axis.AxisTraceMapForm

namespace D5.S3.Axis.TraceMap.Theorem635

open Real
open D5.S3.Axis.AxisTraceRecurrence
open D5.S3.Axis.AxisPartialSum
open D5.S3.Axis.AxisOrbitMap

/-- The theorem its three clauses were carved out of, assembled.

Each clause was proved separately and none is restated. What this adds is that the three
hold of **one** pair of sequences at once: the objects clause one defines are the objects
clause two runs the recurrences on, and the state clause three iterates is built from those
same two sequences. A reader who has the three clauses still has to take that on trust;
here it is a proof term.

The convergence the source records at the end of clause three rests on a numerical
certificate rather than an argument, and is not claimed. -/
theorem axis_trace_map_theorem (x y : ℝ) :
    ((∀ K : ℕ, axisWeight x y K = Real.exp (-x * goldenRatio ^ (K + 1) +
          y * goldenConj ^ (K + 1))) ∧
        (∀ K : ℕ, axisPartialSum x y K =
            ∑ n ∈ Finset.range (Nat.fib (K + 1)), wordWeight x y n) ∧
          ∀ n K : ℕ, Nat.greatestFib n ≤ K ↔ n < Nat.fib (K + 1)) ∧
      ((∀ K : ℕ, axisPartialSum x y (K + 2) =
            axisPartialSum x y (K + 1) + axisWeight x y (K + 2) * axisPartialSum x y K) ∧
          ∀ K : ℕ, axisWeight x y (K + 2) = axisWeight x y (K + 1) * axisWeight x y K) ∧
        ((∀ w₁ w₀ t₁ t₀ : ℝ,
              orbitMap (w₁, w₀, t₁, t₀) = (w₁ + t₁ * t₀ * w₀, w₁, t₁ * t₀, t₁)) ∧
            (∀ K : ℕ, orbitMap (axisState x y K) = axisState x y (K + 1)) ∧
              ∀ K : ℕ, axisState x y K = (orbitMap^[K]) (axisState x y 0)) :=
  ⟨D5.S3.Axis.AxisTraceDefinitions.axis_trace_definitions x y,
    D5.S3.Axis.AxisRecurrencePair.axis_recurrence_pair x y,
    D5.S3.Axis.AxisTraceMapForm.axis_trace_map_form_package x y⟩

end D5.S3.Axis.TraceMap.Theorem635
