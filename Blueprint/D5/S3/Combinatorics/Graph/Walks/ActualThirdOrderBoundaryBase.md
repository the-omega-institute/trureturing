# Initializing the Third Actual Boundary Order

## Abstract

Eight literal third-order joint paths construct both four-path boundaries of the same actual cycle.

**Theorem 1.1 (Initialize Both Actual Third-Order Boundaries).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualThirdOrderBoundaryBase.actual_third_order_boundary_base`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualThirdOrderBoundaryBase.actual_third_order_boundary_base` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sixteen distinct labelled ports specify the two groups of four real cuts. The supplied current Hamilton cycle is partitioned by its eight actual joint paths. Restore each opposite group with explicit walk append, reversal and seam cons operations. The resulting primary and opposite four-path families exhaust that same cycle and delete precisely their own cut groups. The output also exposes the literal crossing and distinguished prefix of the first opposite boundary, for the subsequent simultaneous update.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualThirdOrderBoundaryBase.actual_third_order_boundary_base`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/ActualSimultaneousBoundaryAdvance](ActualSimultaneousBoundaryAdvance.md)
