# The direction partition from a positive Laurent identity

## Abstract

Laurent coefficients determine the direction partition of a cubic support in Q9

**Theorem 1.1 (Positive real weights determine the Laurent row identity).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9LaurentGainPartition.laurentIdentity_iff_evaluateLaurent`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9LaurentGainPartition.laurentIdentity_iff_evaluateLaurent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of the Laurent sums at every strictly positive weight vector is equivalent to equality of their coefficients. Shift both finite exponent sets by the same vector to obtain ordinary polynomials. Polynomial uniqueness on a product of infinite sets recovers equality after the shift, and subtracting the shift recovers the original exponent multiplicities.

**Theorem 1.2 (Reversing a two-step path determines the matched axis).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9LaurentGainPartition.path_exponent_and_gain`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9LaurentGainPartition.path_exponent_and_gain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the Laurent identity at every selected vertex of one parity. The row has one monomial for each directed internal two-step path that does not backtrack. The coefficient of an exponent counts all paths with that exponent. On the other side of the identity, each missing direction contributes its square once.

For a path with axes i and j, add the forward and reverse exponent equations. The potential differences cancel. The two square axes must then be i and j, and the forward square cannot use the internal first axis i. It uses j, which gives the gain e_j − e_i.

**Theorem 1.3 (The internal direction triples of the three neighbors partition the axes).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9LaurentGainPartition.neighbor_triples_partition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9LaurentGainPartition.neighbor_triples_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each selected vertex of that same parity, each missing axis appears in exactly one two-step path because its square coefficient is one. Each internal axis appears at exactly the neighbor across that axis, where it is the returning direction. Cubicity makes the resulting three sets triples.

Where the weighted Huang kernel yields this Laurent identity, the two theorems give necessary local constraints on the support. The support size question is Hong, Wu and Xia’s Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9LaurentGainPartition.laurentIdentity_iff_evaluateLaurent`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9LaurentGainPartition.neighbor_triples_partition`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9LaurentGainPartition.path_exponent_and_gain`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary](../BalancedCubeComponentBoundary.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicHuang](Q9IsotropicHuang.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PureExteriorLink](Q9PureExteriorLink.md)
