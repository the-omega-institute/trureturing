# Time-Ordered Memory Chronology Signature Bridge

## Abstract

The step-two logarithm of the frozen time-ordered memory matrices recovers the oriented swap curvature and specializes the finite Hopf reversal law.

**Theorem 1.1 (Nonzero swap curvature detects event order).**

$$\operatorname{primeSwapCurvature} \neq 0 \Rightarrow\\{}\operatorname{doubledMagnusDegreeTwo} \neq 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MemoryChronology/TimeOrderedMemoryChronologySignatureBridge.timed_matrix_two_event_order_detected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The matrix-valued step-two chronological signature has commutator logarithm. Its upper-right entry is the negative of the already frozen two-event memory swap curvature, due to the reverse matrix-product convention for earlier-first evolution.

The same adapter specializes the chronological Hopf antipode: reverse the timed event word and negate each event matrix. No infinite signature or continuous Magnus convergence is asserted.

## References

- Truth anchor: `D5/S3/Observer/MemoryChronology/TimeOrderedMemoryChronologySignatureBridge.timed_matrix_two_event_order_detected`
- Dependency: [D5/S3/Observer/AgencyHolonomy/TimeOrderedMemoryMatrixRepresentation](../AgencyHolonomy/TimeOrderedMemoryMatrixRepresentation.md)
- Dependency: [D5/S3/Observer/Chronology/ChronologicalSignatureHopf](../Chronology/ChronologicalSignatureHopf.md)
