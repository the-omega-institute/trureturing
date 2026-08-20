# Local Distance Recurrence Uniqueness

## Abstract

The local readout recurrence uniquely fixes the shortest distinguishing distance.

**Theorem 1.1 (The local recurrence uniquely fixes shortest distance).**

$$\begin{gathered}\forall Y, O,\\tau: Y \to Y, q: Y \to O,\\delta: Y \to \left(Y \to \operatorname{Option}\left(\mathbb{N}\right)\right),\\\operatorname{LocalDistanceChecks}\left(tau, q, delta\right) \Rightarrow\\delta = \operatorname{shortestDistance}\left(tau, q\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/PredictionCertificates/LocalDistanceRecurrenceUniqueness.local_recurrence_uniquely_determines_shortest_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Represent an extended natural number by Option Nat, with none denoting infinity. A current readout mismatch forces distance zero. When the readouts agree, the distance is the successor of the next-pair distance, with successor preserving infinity.

The canonical table is constructed from the least future time at which the two readouts differ, and is infinite when no such time exists. Thus the source object is defined by first mismatch, independently of the equality proved here.

The exact repository theorem local_distance_eq_shortest already proves the full statement and is applied directly. Pinned Mathlib grep found no equal first-mismatch recurrence theorem.

## References

- Truth anchor: `D5/S3/ObserverMemory/PredictionCertificates/LocalDistanceRecurrenceUniqueness.local_recurrence_uniquely_determines_shortest_distance`
- Dependency: [D5/S3/ObserverMemory/PredictionCertificates/LocalCertificateMinimality](LocalCertificateMinimality.md)
