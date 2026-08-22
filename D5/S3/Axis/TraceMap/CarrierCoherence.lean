/- GID: D5/S3/Axis/TraceMap/CarrierCoherence
   generality: I
   mirror-B: D5/B/S3/Axis/TraceMap/CarrierCoherence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The two named partial sums agree after one parameter substitution and one depth shift. -/

import D5.S1.Recurrence.TraceMap
import D5.S3.Axis.TraceMap.PartialSumBridge

namespace D5.S3.Axis.TraceMap.CarrierCoherence

open Real
open D5.S1.Recurrence.TraceMap (tracePartial wordSum)
open D5.S3.Axis.AxisPartialSum (axisPartialSum)

/- Errata for `PartialSumBridge`, carried here because that module is frozen.

Its docstring says it "proves the exact relation, so that a statement about one is a statement
about the other". That overstates its type. The theorem there relates `wordSum` at weight index
`j + 2` to `axisPartialSum`; it says nothing about `tracePartial`, which is `wordSum` at weight
index `i + 1`, and the two `axisWeight` constants agreeing at equal indices does not remove that
one-step mismatch. A review seat established the gap mechanically: no theorem in the repository
named both partial sums.

A second, smaller thing is frozen in there too: that module's base case carries an unused
`simp` argument `hz1`, and the three lines deriving it are dead. The linter reports it on every
build. It cannot be removed for the same reason, and is recorded here rather than left as an
unexplained warning.

This module closes the first gap. The missing step is not combinatorial at all: shifting the weight
index by one is exactly substituting `(x, y) ↦ (x * φ, y * ψ)`, because the weight is an
exponential in `φ ^ (k + 1)` and `ψ ^ (k + 1)`. With that, the bridge transports to a
statement about the two carriers the digestion ledger actually names. -/

/-- Shifting the axis weight one step up is the same as scaling the two readings by the
corresponding embedding. -/
theorem axisWeight_succ_eq_scaled (x y : ℝ) (k : ℕ) :
    D5.S3.Axis.AxisTraceRecurrence.axisWeight x y (k + 1) =
      D5.S3.Axis.AxisTraceRecurrence.axisWeight (x * goldenRatio) (y * goldenConj) k := by
  simp only [D5.S3.Axis.AxisTraceRecurrence.axisWeight]
  congr 1
  ring

/-- Set A's `axisWeight` and Set B's are the same function, written twice eight days apart. -/
theorem axisWeight_agree (x y : ℝ) (k : ℕ) :
    D5.S1.Recurrence.TraceMap.axisWeight x y k =
      D5.S3.Axis.AxisTraceRecurrence.axisWeight x y k := by
  simp only [D5.S1.Recurrence.TraceMap.axisWeight,
    D5.S3.Axis.AxisTraceRecurrence.axisWeight]
  congr 1
  ring

/-- The two partial sums the digestion ledger names, related directly: substituting the two
embeddings into the readings and shifting the depth by one carries one onto the other. -/
theorem tracePartial_eq_axisPartialSum (x y : ℝ) (K : ℕ) :
    tracePartial (x * goldenRatio) (y * goldenConj) K = axisPartialSum x y (K + 1) := by
  have hbridge :=
    D5.S3.Axis.TraceMap.PartialSumBridge.wordSum_eq_axisPartialSum x y K
  rw [← hbridge, tracePartial]
  refine congrArg (fun w => wordSum w K) ?_
  funext i
  rw [axisWeight_agree, ← axisWeight_succ_eq_scaled]

end D5.S3.Axis.TraceMap.CarrierCoherence
