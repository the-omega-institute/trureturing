# Last-coordinate fold

## Abstract

Integer channels of the last-coordinate Huang fold

The transverse row constraint applies to the 78-point component case in Hong, Wu and Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, Section 7, Problem 2. Divisibility by four constrains the signs of singleton layers, while the vanishing row at a positive axial dimer supplies the exact equality against which to test those signs. https://arxiv.org/html/2610.09483v1#Thmproblem2

**Definition 1.1 (Last-coordinate reflection).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/HuangLastCoordinateFold.lastFlip`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/HuangLastCoordinateFold.lastFlip` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a vertex x of Q(n + 1), T(x) flips the last bit of x. Applying T twice returns x.

**Definition 1.2 (Transverse Huang row).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/HuangLastCoordinateFold.transverseAction`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/HuangLastCoordinateFold.transverseAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an integer vector on Q(n + 1), the transverse row B at x sums the signed contributions in the first n directions with the original Huang signs.

**Theorem 1.3 (Reflection commutes with the full Huang action).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/HuangLastCoordinateFold.last_flip_commutes`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/HuangLastCoordinateFold.last_flip_commutes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sign of a direction depends only on the bits strictly before it. The proof follows the sign recursion to show that changing a bit at or after that direction preserves the sign. Since coordinate flips commute, the terms in A(f ∘ T)(x) and (Af)(T(x)) agree direction by direction.

**Theorem 1.4 (Transverse equations for the signed channels).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/HuangLastCoordinateFold.transverseAction_channels`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/HuangLastCoordinateFold.transverseAction_channels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Af = λf for an integer vector f on Q(n + 1) and let s(x) be the sign of the last edge at x. Reflection preserves the eigenvalue. Set u = f + f ∘ T and v = f − f ∘ T. The involution fixes u and negates v, and both vectors remain integral. Subtracting the last-edge term from each full row gives (Bu)(x) = (λ − s(x))u(x) and (Bv)(x) = (λ + s(x))v(x).

**Theorem 1.5 (Divisibility and vanishing on the nine-cube).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/HuangLastCoordinateFold.q9_antisymmetric_row`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/HuangLastCoordinateFold.q9_antisymmetric_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an integer 3-eigenvector of the unweighted Huang action on Q₉, a positive last edge gives (Bv)(x) = 4v(x), so the antisymmetric transverse row is divisible by four. If the two axial values agree, v(x) = 0 and the row vanishes for either last-edge sign.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/HuangLastCoordinateFold.lastFlip`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/HuangLastCoordinateFold.last_flip_commutes`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/HuangLastCoordinateFold.q9_antisymmetric_row`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/HuangLastCoordinateFold.transverseAction`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/HuangLastCoordinateFold.transverseAction_channels`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicHuang](../ComponentBoundary/Q9IsotropicHuang.md)
