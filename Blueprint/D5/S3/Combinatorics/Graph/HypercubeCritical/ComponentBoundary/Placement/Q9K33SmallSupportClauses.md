# Corner and support-size clauses for the contact rectangles

## Abstract

The selected supports satisfy the direction-pair and size clauses used by the refutation.

**Theorem 1.1 (Direction-pair witnesses satisfy the corner clauses).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33SmallSupportClauses.pairClause`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33SmallSupportClauses.pairClause` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A variable records a cube point and its two selected flips. A realized corner makes the disjunction over the possible points true.

**Theorem 1.2 (Escape from a support of size below sixty).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33SmallSupportClauses.sizeClause`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33SmallSupportClauses.sizeClause` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any component of size at least sixty has a vertex outside any listed set of fewer than sixty vertices. Seven instances supply the size clauses in the refutation.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33SmallSupportClauses.pairClause`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33SmallSupportClauses.sizeClause`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightDistanceTwoCNF](Q9TightDistanceTwoCNF.md)
