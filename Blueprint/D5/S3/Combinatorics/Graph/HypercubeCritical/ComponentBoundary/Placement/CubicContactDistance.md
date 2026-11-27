# Five coordinates of agreement

## Abstract

Closest pairs of induced cubic cube supports with Huang balance on one side.

**Theorem 1.1 (Five agreement axes for a closest pair).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/CubicContactDistance.closest_pair_distance_add_five_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/CubicContactDistance.closest_pair_distance_add_five_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a closest pair, either endpoint can have neighbors only along axes where the endpoints agree. With at most four agreement axes, the two sets of three neighbor directions share an axis. Flipping that axis at both endpoints preserves distance and agreement. The old and new vertices in the balanced support share only the flipped direction, since another shared direction would complete a coordinate square. Their two sets of three directions therefore require five distinct agreement axes.

**Theorem 1.2 (The closest distances for the nine-cube problem).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/CubicContactDistance.exists_two_components_at_distance_two_to_four`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/CubicContactDistance.exists_two_components_at_distance_two_to_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A hypothetical 258-point support of induced maximum degree three contains two actual balanced cubic components. A closest pair between them has distance at least two by component separation and at most four by the five agreement axes. This gives the three distance cases in Hong, Wu and Xia’s Problem 2. <https://arxiv.org/html/2610.09483v1#Thmproblem2>

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/CubicContactDistance.closest_pair_distance_add_five_le`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/CubicContactDistance.exists_two_components_at_distance_two_to_four`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary](../../BalancedCubeComponentBoundary.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeGirth](../../BalancedCubeGirth.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/TwoBalancedComponents](../../TwoBalancedComponents.md)
