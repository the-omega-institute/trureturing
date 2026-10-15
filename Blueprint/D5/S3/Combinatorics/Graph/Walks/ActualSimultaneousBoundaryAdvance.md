# Two Actual Boundary Orders of the Same Cycle

## Abstract

One actual joint update constructs both restored boundary orders on the same supplied cycle.

**Theorem 1.1 (Advance Both Actual Boundary Orders).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualSimultaneousBoundaryAdvance.actual_simultaneous_boundary_advance`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualSimultaneousBoundaryAdvance.actual_simultaneous_boundary_advance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The supplied prior cycle has actual joint, primary and opposite partitions with disjoint cut groups. The current supplied Hamilton cycle has the earned three-path joint replacement. After the cut groups exchange and their new zero cuts are erased, explicit restoration constructs both actual next boundaries at once. Every output path is simple; all three partitions refer to the same current cycle. The complete endpoint sets and the literal distinguished and crossing prefixes needed by the next step are conclusions.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualSimultaneousBoundaryAdvance.actual_simultaneous_boundary_advance`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/ActualPriorBoundaryInputs](ActualPriorBoundaryInputs.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/ActualSingleOrderBoundaryUpdate](ActualSingleOrderBoundaryUpdate.md)
