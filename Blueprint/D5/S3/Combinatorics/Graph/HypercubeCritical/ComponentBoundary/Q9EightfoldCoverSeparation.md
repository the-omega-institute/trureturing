# Distinct eightfold edges have disjoint selected shells

## Abstract

Distinct eightfold edges have disjoint selected shells

**Theorem 1.1 (Distinct eightfold edges have disjoint selected shells).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightfoldCoverSeparation.eightfold_cover_shells_disjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightfoldCoverSeparation.eightfold_cover_shells_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every endpoint of one eightfold cover is at Hamming distance at least four from each endpoint of another for the same support.

A distance-two pair would give opposite sign products by the negative square, but equal products by the corner rule. At distance three two directions have the same phase and force an extra exterior neighbor.

The distance bound separates the transverse first shells from each other and from the other second shell. A shared second-shell vertex would have two selected neighbors in each disjoint first shell, contradicting cubicity.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightfoldCoverSeparation.eightfold_cover_shells_disjoint`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightfoldCoverLocal](Q9EightfoldCoverLocal.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CubeSmallSupport](../CubeSmallSupport.md)
