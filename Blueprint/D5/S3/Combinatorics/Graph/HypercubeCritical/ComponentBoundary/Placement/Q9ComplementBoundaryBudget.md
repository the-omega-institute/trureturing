# The edge budget of the complement

## Abstract

A 258-vertex subcubic restriction of the nine-cube leaves room for at most 369 omitted edges.

**Theorem 1.1 (At most 738 oriented complement edges).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ComplementBoundaryBudget.complement_darts_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ComplementBoundaryBudget.complement_darts_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A 258-vertex induced subcubic set sends at least six edges per vertex to its complement. Edge reversal counts these incidences at the complement, whose 254 vertices have ambient degree nine. At most 738 oriented edges then remain inside the complement.

**Theorem 1.2 (Internal and crossing edges share the budget).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ComplementBoundaryBudget.packed_darts_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ComplementBoundaryBudget.packed_darts_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two disjoint subsets of a finite vertex set of the nine-cube, their internal edges and their crossing edges contribute twice each to the total number of oriented edges in that vertex set.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ComplementBoundaryBudget.complement_darts_le`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ComplementBoundaryBudget.packed_darts_le`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ExteriorEdgeLiftCount](Q9ExteriorEdgeLiftCount.md)
