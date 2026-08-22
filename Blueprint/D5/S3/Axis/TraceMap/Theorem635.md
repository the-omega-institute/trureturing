# Theorem 635

## Abstract

The three clauses of the axis trace map theorem hold of one pair of sequences.

The theorem was carved into three clauses: the two objects and the bridge that makes the summation bound mean bounded depth, the pair of recurrences those objects satisfy, and the four coordinate map whose orbit carries the axis state.

Each clause was proved on its own and none is restated. What this adds is that the three hold of one pair of sequences at once. Read separately, a reader has to check by eye that the objects the first clause defines are the ones the second runs recurrences on, and that the state the third iterates is built from those same two sequences. Assembled, that is a proof term instead.

Replacing the second reading by a copy of the first in the third block makes the module fail to build, so the shared parameters carry weight rather than appearing to. The convergence the source records at the end of the third clause rests on a numerical certificate rather than an argument, and is not claimed.

**Theorem 1.1 (The three clauses assembled).**

$$\operatorname{W}\left(K\right) = \operatorname{sum}\left(\operatorname{range}\left(\operatorname{fib}\left(K + 1\right)\right), \operatorname{wordWeight}\left(\right)\right) \land \left(\operatorname{W}\left(K + 2\right) = \operatorname{W}\left(K + 1\right) + \operatorname{t}\left(K + 2\right) \cdot \operatorname{W}\left(K\right) \land \operatorname{F}\left(\operatorname{state}\left(K\right)\right) = \operatorname{state}\left(K + 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/TraceMap/Theorem635.axis_trace_map_theorem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One conjunction over the same two parameters, carrying the definitions and their bridge, the pair of recurrences, and the map with its orbit.

## References

- Truth anchor: `D5/S3/Axis/TraceMap/Theorem635.axis_trace_map_theorem`
- Dependency: [D5/S3/Axis/AxisRecurrencePair](../AxisRecurrencePair.md)
- Dependency: [D5/S3/Axis/AxisTraceDefinitions](../AxisTraceDefinitions.md)
- Dependency: [D5/S3/Axis/AxisTraceMapForm](../AxisTraceMapForm.md)
