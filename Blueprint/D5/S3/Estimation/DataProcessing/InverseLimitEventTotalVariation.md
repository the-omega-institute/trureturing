# Total Variation on Compatible Threads

## Abstract

The full event distance between two finite laws on a finite-alphabet inverse limit is the supremum of the distances between their actual level projections.

**Theorem 1.1 (All measurable events are controlled by level laws).**

$$\begin{aligned}\forall P, Q \in \operatorname{FiniteMeasures}\left(X\right),\\\operatorname{TV}\left(P, Q\right) = \operatorname{sup}_{l \in \mathbb{N}} \operatorname{TV}\left(\operatorname{push}\left(pi_{l}, P\right), \operatorname{push}\left(pi_{l}, Q\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/InverseLimitEventTotalVariation.total_variation_eq_iSup_level` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A thread is a sequence whose adjacent coordinates obey the prescribed bonding maps. The sample space consists of a fixed finite tuple of threads. A level projection reads that same level at every node.

Every alphabet is finite and every singleton is measurable. Both measures are finite. The statement allows arbitrary bonding maps, arbitrary tuple length, zero-mass labels, and laws without feasibility constraints.

The inherited measurable structure is the Borel structure when the alphabets carry their discrete topologies. Total variation takes the supremum over all measurable events of the maximum of the two directed truncated measure differences.

Compatibility lifts two cylinder events to a common higher level. These events form a ring that generates the entire measurable structure. Approximation in the sum of the two measures then transfers the cylinder bound to every measurable event.

This identity compares two given laws. It does not select a compatible family from separate finite feasible sets or assert that a nearest feasible law exists.

## References

- Truth anchor: `D5/S3/Estimation/DataProcessing/InverseLimitEventTotalVariation.total_variation_eq_iSup_level`
- Dependency: [D5/S3/Estimation/DataProcessing/MeasurablePostprocessingDefectContraction](MeasurablePostprocessingDefectContraction.md)
