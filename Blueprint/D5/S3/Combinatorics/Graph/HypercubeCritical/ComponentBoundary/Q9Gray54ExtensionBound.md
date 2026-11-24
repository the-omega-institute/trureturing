# Extending a Gray54 component

## Abstract

The Gray54 extension bound in the nine-cube

**Theorem 1.1 (At most 257 vertices in a subcubic extension).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9Gray54ExtensionBound.card_le_of_balanced_cubic_fifty_four`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9Gray54ExtensionBound.card_le_of_balanced_cubic_fifty_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reconstruct the 54-vertex Huang-balanced cubic support as a cube symmetry of the standard Gray pattern. Because that support is closed under selected neighbors, its image in the standard coordinates leaves the additional vertices outside its closed neighborhood. The residual subgraph has 314 vertices, and its selected subgraph has maximum degree at most three.

Start with charge 3888 times the difference between each selection indicator and that of the 203-vertex reference set. Average 25 signed transfers over block permutations and permutations within the blocks. Each transfer contributes opposite charges at its endpoints. The total therefore equals 3888 times the excess over 203, while each local charge only uses the vertices at distance at most one. The finite checks for 15 block-weight profiles bound the total charge by 3672. Integrality allows at most 203 residual vertices.

This excludes a Gray54 component in a 258-vertex subcubic support in Hong–Wu–Xia's Problem 2, arXiv:2610.09483v1, §7.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9Gray54ExtensionBound.card_le_of_balanced_cubic_fifty_four`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CubicFiftyFourReconstruction](../CubicFiftyFourReconstruction.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/TwoBalancedComponents](../TwoBalancedComponents.md)
