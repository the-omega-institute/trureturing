/- GID: D5/S3/Axis/TraceMap/ContainerWitness
   generality: I
   mirror-B: D5/B/S3/Axis/TraceMap/ContainerWitness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One statement naming the parent receipt's carrier and the whole child package. -/

import D5.S3.Axis.TraceMap.CarrierCoherence
import D5.S3.Axis.TraceMap.Theorem635

namespace D5.S3.Axis.TraceMap.ContainerWitness

open Real
open D5.S1.Recurrence.TraceMap (tracePartial trace_map_recursion)
open D5.S3.Axis.AxisPartialSum (axisPartialSum)

/- The container atom `theorem/6.35` carries a pre-committed receipt naming
`D5/S1/Recurrence/TraceMap.trace_map_recursion`, while its three clause atoms are covered by
declarations in `D5/S3/Axis`. A review seat rejected settling the container until one Closed
statement named both sides, on the ground that covering the parent against a carrier its
children do not use would certify an equivalence nobody had proved.

This is that statement. It conjoins three things and invents none of them:

* the recurrence pair the parent receipt's own carrier proves, at the substituted readings;
* the coherence relation carrying that carrier onto the one the children use;
* the child package itself, which covers the definitions, the recurrences and the map.

Nothing here is restated: each conjunct is an existing theorem applied. What the conjunction
adds is that they hold of one pair of readings at once, which is exactly what the parent
receipt and the child coverage would otherwise be asserting separately and on trust. -/

/-- The parent receipt's carrier, the coherence relation, and the child package, at one pair
of readings. -/
theorem container_witness (x y : ℝ) (K : ℕ) :
    (tracePartial (x * goldenRatio) (y * goldenConj) (K + 2) =
          tracePartial (x * goldenRatio) (y * goldenConj) (K + 1) +
            D5.S1.Recurrence.TraceMap.axisWeight
              (x * goldenRatio) (y * goldenConj) (K + 2) *
              tracePartial (x * goldenRatio) (y * goldenConj) K ∧
        D5.S1.Recurrence.TraceMap.axisWeight (x * goldenRatio) (y * goldenConj) (K + 2) =
          D5.S1.Recurrence.TraceMap.axisWeight (x * goldenRatio) (y * goldenConj) (K + 1) *
            D5.S1.Recurrence.TraceMap.axisWeight (x * goldenRatio) (y * goldenConj) K) ∧
      (∀ J : ℕ, tracePartial (x * goldenRatio) (y * goldenConj) J =
          axisPartialSum x y (J + 1)) ∧
        (∀ J : ℕ, D5.S3.Axis.AxisTraceRecurrence.axisWeight x y J =
              Real.exp (-x * goldenRatio ^ (J + 1) + y * goldenConj ^ (J + 1))) ∧
          ∀ J : ℕ, D5.S3.Axis.AxisPartialSum.axisPartialSum x y (J + 2) =
              D5.S3.Axis.AxisPartialSum.axisPartialSum x y (J + 1) +
                D5.S3.Axis.AxisTraceRecurrence.axisWeight x y (J + 2) *
                  D5.S3.Axis.AxisPartialSum.axisPartialSum x y J :=
  ⟨trace_map_recursion (x * goldenRatio) (y * goldenConj) K,
    fun J => D5.S3.Axis.TraceMap.CarrierCoherence.tracePartial_eq_axisPartialSum x y J,
    fun _ => rfl,
    D5.S3.Axis.AxisPartialSum.axisPartialSum_succ_succ x y⟩

end D5.S3.Axis.TraceMap.ContainerWitness
