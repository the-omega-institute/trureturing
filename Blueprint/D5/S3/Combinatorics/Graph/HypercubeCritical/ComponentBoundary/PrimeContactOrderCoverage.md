# Coordinate permutation coverage by integer exponent gains

## Abstract

Coordinate permutation coverage by integer exponent gains

**Theorem 1.1 (The total local cover contains at least all coordinate permutations).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactOrderCoverage.card_perm_le_sum_card_localOrders`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactOrderCoverage.card_perm_le_sum_card_localOrders` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The collection of all local order sets covers the coordinate permutations. The union bound compares its cardinality with the sum of the local cardinalities.

**Theorem 1.2 (Each coordinate order occurs in at least one local maximum).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactOrderCoverage.exists_mem_localOrders`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactOrderCoverage.exists_mem_localOrders` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Maximize the scalar product of an integer exponent potential with the ranks of a coordinate permutation over a finite nonempty set of columns. Each available step adds one source axis and subtracts its target axis. Maximality and distinct ranks force each target to have larger rank than all sources in its block.

**Theorem 1.3 (Four exponent steps give the eight-axis weighted covering inequality).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactOrderCoverage.weighted_order_coverage`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactOrderCoverage.weighted_order_coverage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Independent permutations within disjoint blocks act on coordinate orders and carry each fibre of the block maxima bijectively to every other fibre. With four source axes and disjoint blocks of size two or three, the possible products of block sizes are sixteen, twelve and nine. The permutation fibres have respectively 2520, 3360 and 4480 members out of 40320. The union covers all permutations, yielding the bound 144 by the weighted column counts 9, 12 and 16.

In the eight transverse coordinates of the paired-fibre analysis for Hong, Wu and Xia's Problem 2, the counts distinguish columns with different numbers of two-source targets. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactOrderCoverage.card_perm_le_sum_card_localOrders`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactOrderCoverage.exists_mem_localOrders`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactOrderCoverage.weighted_order_coverage`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactTransport](PrimeContactTransport.md)
