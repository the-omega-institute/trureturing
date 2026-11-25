# Higher-contact covers of coordinate orders

## Abstract

Higher-contact covers of coordinate orders

**Theorem 1.1 (Opposing contacts of higher coordinate rank).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/GeneralContactOrderCoverage.exists_signed_higher_contact`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/GeneralContactOrderCoverage.exists_signed_higher_contact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose geometric weights in any coordinate order and a largest nonzero kernel coefficient. The signed contribution on every incident empty row must be canceled by an opposing term of strictly higher rank, since the sum of all lower-rank terms is too small.

**Theorem 1.2 (Coordinate permutations cover the columns).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/GeneralContactOrderCoverage.factorial_le_sum_card_cubeOrders`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/GeneralContactOrderCoverage.factorial_le_sum_card_cubeOrders` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A column covers an order when every empty axis has a higher-ranked neighbor in the local double-flip graph. Counting the covering union gives a factorial bound for arbitrary row multiplicities. Relabeling coordinates acts by permutation on the order sets.

**Theorem 1.3 (Actual two-component necessary condition).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/GeneralContactOrderCoverage.exists_two_components_with_higherContact_orderCoverage`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/GeneralContactOrderCoverage.exists_two_components_with_higherContact_orderCoverage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each dominant axis of a 258-vertex subcubic support, each of the two selected components has a fixed projected parity and must pass the order-cover bound 40320. Full parity chooses a representative of each pair. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/GeneralContactOrderCoverage.exists_signed_higher_contact`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/GeneralContactOrderCoverage.exists_two_components_with_higherContact_orderCoverage`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/GeneralContactOrderCoverage.factorial_le_sum_card_cubeOrders`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactOrderCoverage](PrimeContactOrderCoverage.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9DominantAxisBoundary](../CoordinateHalves/Q9DominantAxisBoundary.md)
