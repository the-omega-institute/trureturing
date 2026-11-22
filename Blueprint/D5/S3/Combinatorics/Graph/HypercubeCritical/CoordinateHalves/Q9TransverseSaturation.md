# Transverse incidences in cubic nine-cube supports

## Abstract

Transverse incidences in cubic nine-cube supports

**Theorem 1.1 (A minority edge cannot meet all transverse directions).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TransverseSaturation.no_cubic_minority_transverse_saturation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TransverseSaturation.no_cubic_minority_transverse_saturation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Count each induced edge in a coordinate direction at its endpoint with that coordinate false. If each chosen parity class has one or four edges, the four transverse incidences from one size-four axis force all classes to have size four. The incidences from every other axis then exhaust each class. A single edge would meet eight transverse directions, whereas the two endpoints have only four incident edges besides their common edge.

In Hong, Wu and Xia's separated 120+138 branch, the signed contact-block classification supplies two K4,4 covers for a 16+4 fold. In each cover and transverse direction, two contacts occur in each axial layer, which supplies two edges of each parity. The two covers together give the four incidences required by the theorem. The classification and its search completeness are inputs to this application. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TransverseSaturation.no_cubic_minority_transverse_saturation`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary](../BalancedCubeComponentBoundary.md)
