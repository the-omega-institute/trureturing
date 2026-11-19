# Parity of Boolean weight layers

## Abstract

WeightLayerParity

The parity of the selected degree at any cube vertex equals its membership indicator. Summing this relation over an odd weight layer pairs that layer with the preceding even layer. At order 66, the odd layers total 33 vertices, so the total Boolean weight is congruent to one modulo four. The coordinate half sizes then force an even total deficit. This constrains the 66-vertex case of Hong–Wu–Xia Section 7 Problem 2.

**Theorem 1.1 (Consecutive layers have equal parity).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/WeightLayerParity.balanced_cube_even_adjacent_layers`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/WeightLayerParity.balanced_cube_even_adjacent_layers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every even weight from zero through eight, the combined size of that layer and its successor is even in a Huang-balanced induced cubic support.

**Theorem 1.2 (The total deficit is even).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/WeightLayerParity.balanced_sixty_six_even_total_deficit`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/WeightLayerParity.balanced_sixty_six_even_total_deficit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a 66-vertex Huang-balanced induced cubic support, write each coordinate true-half size as thirty-three minus twice its deficit. The sum of the nine deficits is even.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/WeightLayerParity.balanced_cube_even_adjacent_layers`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/WeightLayerParity.balanced_sixty_six_even_total_deficit`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary](../BalancedCubeComponentBoundary.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CubicFiftyFourReconstruction](../CubicFiftyFourReconstruction.md)
