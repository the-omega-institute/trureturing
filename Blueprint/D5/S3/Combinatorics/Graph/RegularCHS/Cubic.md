# Closed walks in regular graphs

## Abstract

Closed walk lower bounds and cubic graph moment domination.

**Theorem 1.1 (Reversing walks gives even moment lower bounds).**

Lean statement: `D5/S3/Combinatorics/Graph/RegularCHS/Cubic.closedWalks_ge_of_minDegree`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/RegularCHS/Cubic.closedWalks_ge_of_minDegree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite simple graph on n vertices whose degrees are at least r, the total number of rooted closed walks of length 2j is at least n times r to the power j. Symmetry expresses the even moment as the sum of squares of the entries of the jth adjacency power. Each natural number is bounded by its square, and each row sum counts at least r to the power j walks. This also includes j equal to zero.

**Theorem 1.2 (Cubic graphs dominate the cycle in every positive moment).**

Lean statement: `D5/S3/Combinatorics/Graph/RegularCHS/Cubic.closedWalks_cubic_ge_cycle`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/RegularCHS/Cubic.closedWalks_cubic_ge_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every cubic simple graph on n vertices with n at least three, each positive closed walk count is at least the corresponding count of the n-cycle. Connectedness is not required. The cubic second and fourth moments are at least 3n and 15n. Cauchy-Schwarz makes the even moments log convex, so they grow by a factor at least five after the second moment; consequently the moment of order 2j is at least n times 4 to the power j for j at least three. The cycle has at most n times 4 to the power j closed walks of order 2j, and its fourth moment is at most 8n. The degree sum forces n to be even, so the cycle admits a bicoloring and has no odd closed walks.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/RegularCHS/Cubic.closedWalks_cubic_ge_cycle`
- Truth anchor: `D5/S3/Combinatorics/Graph/RegularCHS/Cubic.closedWalks_ge_of_minDegree`
- Dependency: [D5/S3/Combinatorics/Graph/RegularCHS/Interface](Interface.md)
