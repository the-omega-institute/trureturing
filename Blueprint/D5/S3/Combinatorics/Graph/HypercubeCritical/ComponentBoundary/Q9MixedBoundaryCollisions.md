# Collisions between edge translations from two components

## Abstract

Collisions between edge translations from two components

**Theorem 1.1 (Mixed collisions count pairs at distance two).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MixedBoundaryCollisions.sum_mixed_multiplicity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MixedBoundaryCollisions.sum_mixed_multiplicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let C and D be disjoint vertex sets with no edge between them. For an exterior edge e, let m_C(e) and m_D(e) count coordinate flips carrying e to an internal edge of C and D, respectively. The sum of m_C(e)m_D(e) equals the number of triples (c,d,t) in which c ∈ C and d ∈ D have Hamming distance two and both have an internal edge in direction t. Distinguishing an endpoint of e produces two choices for each pair of flips. On the distance-two side, the same data distinguish one of the two common neighbors of c and d. The factors of two cancel.

**Theorem 1.2 (A necessary collision count at 258 vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MixedBoundaryCollisions.mixed_collision_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MixedBoundaryCollisions.mixed_collision_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If C and D are closed Huang-balanced induced cubic components of a 258-vertex subcubic U, their union has 6(|C|+|D|) boundary-edge translations counted with multiplicity. The complement of U contains at most 369 edges. For each exterior edge, expanding the second binomial moment of m_C+m_D gives the two within-component counts and the mixed product. Their sum is therefore at least 6(|C|+|D|)−369.

This condition concerns the 258-vertex formulation of Hong–Wu–Xia, arXiv:2610.09483v1, §7 Problem 2 (https://arxiv.org/html/2610.09483v1#Thmproblem2). The value of f₂(Q₉) remains open.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MixedBoundaryCollisions.mixed_collision_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MixedBoundaryCollisions.sum_mixed_multiplicity`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryEdgeTranslations](Q9BoundaryEdgeTranslations.md)
