# Signed boundary and completion bounds

## Abstract

Signed fragments of balanced cubic supports in the nine-cube

**Theorem 1.1 (The known signs force additional contacts).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedFragmentBoundary.card_add_abs_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedFragmentBoundary.card_add_abs_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a fragment of an induced Huang-balanced cubic support with its switching signs. At an exterior vertex, the full Huang row vanishes. Each new contact can cancel at most one unit of the fragment's signed sum. The full contact count is therefore at least the known count plus the absolute value of that sum.

**Theorem 1.2 (A separated support has fewer available contacts).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedFragmentBoundary.shared_contacts_le_of_fragment`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedFragmentBoundary.shared_contacts_le_of_fragment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When a vertex sees the fragment and another disjoint nonadjacent balanced cubic support, the two full supports can use at most six contact directions there. The fragment's known contacts and the contacts needed to cancel its signed sum consume part of that budget before the first support is completed.

**Theorem 1.3 (The signed boundary bounds the order of any completion).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedFragmentBoundary.fragment_size_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedFragmentBoundary.fragment_size_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing the contact bound over the exterior charges every further vertex through its incident edges. Inside the completion, sign coherence makes the absolute signed sum equal to the fragment's contact count. Double counting gives three times the fragment order plus the sum of the absolute signed rows at most six times the completion order.

These inequalities constrain candidate supports for Problem 2 of Hong, Wu and Xia, which asks for a 258-vertex subcubic support in the nine-cube. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedFragmentBoundary.card_add_abs_le`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedFragmentBoundary.fragment_size_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedFragmentBoundary.shared_contacts_le_of_fragment`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary](../BalancedCubeComponentBoundary.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance](../HuangCubeCovariance.md)
