# Capacity of a witnessed face

## Abstract

Four-face packing in subcubic nine-cube supports

**Theorem 1.1 (Two actual components force distinct four-faces).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9ThreeAxisCapacityTransport.two_components_four_face_capacity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9ThreeAxisCapacityTransport.two_components_four_face_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose the two actual components of a 258-point subcubic support before choosing four active coordinates. For each dominant axis, fix one projected parity per component before the transverse mask. Each witness face is anchored at an actual paired vertex of that parity. On the other three axes a masked boundary kernel restricts to a three-cube slice.

The full parity block on that slice is orthogonal up to the squared weight norm. Its unique zero in each row and column is the antipodal position. This forces a rank-deficient restriction to have more paired columns than empty rows, a retained antipodal singleton pair, or an omitted antipodal pair in the three-by-three case.

Restore the dominant axis. In each witness case the complement of the component's closed neighborhood has at most three vertices in the four-face. Every other selected component therefore has to share those three places. A rank witness needs at least five vertices, so the two selected components require different four-faces for the same mask.

These are necessary conditions for a 258-point subcubic support in Hong, Wu and Xia's Problem 2. The four-face labels are the five inactive bits, which also show how the capacity constraints move under XOR translations. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9ThreeAxisCapacityTransport.two_components_four_face_capacity`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedBoundaryGram](../ComponentBoundary/Q9WeightedBoundaryGram.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9DominantAxisBoundary](Q9DominantAxisBoundary.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9FourFaceDefect](Q9FourFaceDefect.md)
