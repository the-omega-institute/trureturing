# The order-two exception to one-side support

## Abstract

A feasible optimal pair in the order-two incidence graph has singletons in both color classes.

**Definition 1.1 (One-side support from order two).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/HeawoodOrderTwoRefutation.claim`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/HeawoodOrderTwoRefutation.claim` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Exact sub-quorum values from C4-free pair packing*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/48728b42d39ab3de5de251c61da5a404ec418a69/docs/C4_FREE_REPRESENTATIVE_EQUALITY.md>.

*Commentary.*

The proposed extension quantifies over every finite simple graph, every proper two-coloring, and every natural order q at least two. The graph must have no four-cycle, have degree q+1 at every vertex, and have q squared plus q plus one vertices in each color class. For every feasible singleton and matching pair of that same objective, the conclusion requires a color class containing all singletons and requires every vertex in that class to be a singleton or a matching endpoint.

**Theorem 1.2 (The binary Heawood counterexample).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/HeawoodOrderTwoRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/HeawoodOrderTwoRefutation.result` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Exact sub-quorum values from C4-free pair packing*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/48728b42d39ab3de5de251c61da5a404ec418a69/docs/C4_FREE_REPRESENTATIVE_EQUALITY.md>.

*Commentary.*

Use the source's binary labeling, with point vertices 0 through 6 and line vertices 7 through 13. Each side has the nonzero three-bit labels in increasing numeric order. Opposite-side vertices are incident when their binary dot product is zero. This graph is cubic and two distinct vertices share at most one neighbor, so there is no four-cycle. The six singletons are {1, 2, 3, 11, 12, 13} and the matching is {(0, 8)}. The matching is disjoint from the singletons, and each singleton has at most one neighbor among the occupied vertices, so the pair is feasible. The point side has singletons {1, 2, 3} and the line side has singletons {11, 12, 13}, three on each side. C4RepresentativeBounds.threshold_parameters at degree three and side size seven gives beta(H,2)=psiSq(H)=Omega(H)=7. The pair attains objective seven and refutes the one-side conclusion at q=2.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/HeawoodOrderTwoRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/HeawoodOrderTwoRefutation.result`
- Dependency: [D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds](C4RepresentativeBounds.md)
