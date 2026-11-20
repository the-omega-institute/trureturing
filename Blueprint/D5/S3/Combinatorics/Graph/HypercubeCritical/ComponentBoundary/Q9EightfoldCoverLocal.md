# The eightfold corner rule

## Abstract

The eightfold corner rule

**Theorem 1.1 (The eightfold corner rule).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightfoldCoverLocal.eightfold_corner_rule`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightfoldCoverLocal.eightfold_corner_rule` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consider an exterior cube edge whose eight transverse translates are all edges of a Huang-balanced cubic support.

The exterior eigenrow has four positive and four negative terms. The edge transports all eight signs by a common factor. An opposite-sign pair contributes exactly one selected corner across the two layers, while an equal-sign pair contributes none.

Anticommutation supplies the sign test, square exclusion prevents double occupancy, and the cubic degrees exhaust the four possible opposite-sign partners. Hence there are exactly sixteen selected corners.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightfoldCoverLocal.eightfold_corner_rule`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MixedBoundaryCollisions](Q9MixedBoundaryCollisions.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance](../HuangCubeCovariance.md)
