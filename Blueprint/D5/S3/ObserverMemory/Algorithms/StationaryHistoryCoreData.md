# StationaryHistoryCoreData

## Abstract

Actual core data from original controller targets.

**Theorem 1.1 (Unrestricted original structural interface).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{[\operatorname {DecidableEq}(Q)][\operatorname {NeZero}(3\times P)]\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {Fintype}(Q)]\operatorname {CoreData}(C,hP,I)}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryCoreData.actual_core_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

CoreData collects the proved actual incidence, degree, two-row, production and resolving counts, selected-target count and outside-B property, target identities and distinct resolving rows, s<=J, pure unary structure, N core and e extra targets, and the original ActualRead cardinal N+1+e. It also contains the disjoint exact target partition, strict binary representative bound, exact binary/selected-literal baseline assignments, all actual tail bounds, core digit occupancy, absence of extra background, and indexed history separation. This is the structural input to the subsequent weighted inventory; it states no overlap correction, weighted necessary inequality, zero-correction theorem, synthesis, or global capacity conclusion.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryCoreData.actual_core_data`
- Dependency: [D5/S3/ObserverMemory/Algorithms/StationaryHistoryCore](StationaryHistoryCore.md)
