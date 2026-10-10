# StationaryHistoryData

## Abstract

Actual history data from original controller histories.

**Theorem 1.1 (Derived actual history data).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {NeZero}(3\times P)]\operatorname {HistoryData}(C,hP,I)}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryData.actual_history_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

HistoryData derives positive bounded read counts, exact first events, event levels, times and colors, nonempty supports, parent levels and support inclusion, and disjoint indexed event fibers. Event and history-label incidence are equivalent. The exact root and leaf cardinalities are three and 3P. Every graph leaf has the fixed original output of each supporting input. Root colors, shifts and levels are c, ell and zero, with the exact first-digit supports. Same-control phase supports are disjoint, time is shift plus level, and every successive read has a positive literal wait equal to its shift increase. Singleton continuations have one child. All these fields are obtained from C and I; interval propagation and binary-node counts are not fields of HistoryData.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryData.actual_history_data`
- Dependency: [D5/S3/ObserverMemory/Algorithms/StationaryHistoryContinuation](StationaryHistoryContinuation.md)
