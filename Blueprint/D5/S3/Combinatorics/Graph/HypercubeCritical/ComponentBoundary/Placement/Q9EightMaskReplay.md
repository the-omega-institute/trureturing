# Exactly eight distance-two masks are impossible

## Abstract

A checked refutation excludes exactly eight distance-two masks.

**Theorem 1.1 (Exactly eight distance-two masks are impossible).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9EightMaskReplay.minimum_displacements_card_ne_eight`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9EightMaskReplay.minimum_displacements_card_ne_eight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each participating axis has three partners or more by signed contact cancellation. The five-axis graph at equality reduces to a single chosen contact orbit. Lean proves that the normalized pair satisfies each of the 11,564 input clauses and replays the 4,104-step LRAT refutation. The certificate needs only the two realized masks {0, 3} and {0, 4}, in addition to the local degree, parity, and separation constraints. <https://arxiv.org/html/2610.09483v1#Thmproblem2>

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9EightMaskReplay.minimum_displacements_card_ne_eight`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9EightMaskClauses](Q9EightMaskClauses.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9EightMaskGraph](Q9EightMaskGraph.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactGeometryReplay](Q9SharedContactGeometryReplay.md)
