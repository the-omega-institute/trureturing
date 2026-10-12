# Rectangular weak two-metric dimension below the threshold

## Abstract

For 4 <= n < m < 2n - 2, the weak two-metric dimension of the rectangular Hamming graph is min(ceil(2(n+m)/3), 2n - 2).

The graph is the Cartesian product of complete graphs on n and m vertices, with Hamming distance on its row and column coordinates. A landmark set is weak two-resolving when the sum of absolute distance differences is at least two for every distinct vertex pair. The rectangular range below m = 2n - 2 is identified in Aryan Kumar, arXiv:2609.32161v1, Section 7. Throughout the displayed statements, natDiv(a,b) denotes natural number division; natDiv(2(n+m)+2,3) equals ceil(2(n+m)/3).

**Theorem 1.1 (The two-thirds upper bound).**

$$\forall n \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; 4 \le n \Rightarrow \left(n < m \Rightarrow \left(m < 2 \cdot n - 2 \Rightarrow \left(\exists S \in \operatorname{Finset}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right)\right)\right),\; \operatorname{IsWeakResolving}\left(2, S\right) \land \operatorname{card}\left(S\right) \le \operatorname{natDiv}\left(2 \cdot \left(n + m\right) + 2, 3\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimension.ceiling_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every 4 <= n < m < 2n - 2, there is a weak two-resolving landmark set of cardinality at most ceil(2(n+m)/3). View landmarks as edges between row and column vertices. Remove one row and two columns when rows are no more numerous than columns, or two rows and one column otherwise, and place a two-edge star on the removed vertices. These reductions preserve positivity and the inequalities that each part has at most twice the size of the other. At a total of three to five vertices, explicit stars or paths complete the construction. Every vertex has positive degree and each edge has endpoint degree sum at least three, so the resulting set is weak two-resolving. Each three-vertex extension adds two edges.

**Theorem 1.2 (The empty-row upper bound).**

$$\forall n \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; 4 \le n \Rightarrow \left(n < m \Rightarrow \left(m < 2 \cdot n - 2 \Rightarrow \left(\exists S \in \operatorname{Finset}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right)\right)\right),\; \operatorname{IsWeakResolving}\left(2, S\right) \land \operatorname{card}\left(S\right) \le 2 \cdot n - 2\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimension.empty_row_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every 4 <= n < m < 2n - 2, there is a weak two-resolving landmark set of cardinality at most 2n - 2. Leave row zero empty. In each row i from one to n - 1, place landmarks in columns 2(i-1) mod m and (2(i-1)+1) mod m. These columns are distinct, and the consecutive residues cover all columns because m <= 2(n-1). Every occupied row has degree two, every column has positive degree, and any disjoint landmarks have total endpoint degree at least six. The pair degree conditions therefore give weak two-resolution.

**Definition 1.3 (The exact rectangular formula).**

$$\mathrm{claim} \Leftrightarrow \left(\forall n \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; 4 \le n \Rightarrow \left(n < m \Rightarrow \left(m < 2 \cdot n - 2 \Rightarrow \operatorname{wdim}\left(n, m, 2\right) = \operatorname{min}\left(\operatorname{natDiv}\left(2 \cdot \left(n + m\right) + 2, 3\right), 2 \cdot n - 2\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimension.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula asserts, for all natural n and m satisfying 4 <= n < m < 2n - 2, equality of the weak two-metric dimension with the smaller of the two-thirds ceiling and 2n - 2.

**Theorem 1.4 (Exact weak two-metric dimension).**

$$\mathrm{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimension.result` (`✓ std3`). ∎

*Resolves.* `Problems/kumar-2026-rectangular-weak-two-metric-dimension` (proved) by `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimension.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kumar-2026-rectangular-weak-two-metric-dimension","declaration_gid":"D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimension.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

The formula holds throughout the stated rectangular range. The degree constraints give the minimum of the two quantities as a lower bound for every resolving set. The two constructions give each quantity as an upper bound, and hence give their minimum as the upper bound as well.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimension.ceiling_upper`
- Truth anchor: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimension.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimension.empty_row_upper`
- Truth anchor: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimension.result`
- Dependency: [D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore](HammingWeakTwoMetricDimensionCore.md)
- Dependency: [D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionLower](HammingWeakTwoMetricDimensionLower.md)
