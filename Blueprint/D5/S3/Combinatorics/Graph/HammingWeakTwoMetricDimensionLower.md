# Reciprocal-degree charging for rectangular Hamming graphs

## Abstract

Endpoint-degree constraints give a sharp lower bound for weak two-resolving landmark sets in rectangular Hamming graphs.

**Theorem 1.1 (Two-thirds incidence bound).**

Lean statement: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionLower.bipartite_degree_charging`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionLower.bipartite_degree_charging` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let I and J be finite types with decidable equality and S a finite subset of I times J. Write g(i) and h(j) for the numbers of members of S incident with i and j. Suppose every g(i) and h(j) is positive, the total number of vertices is at least six, and any two edges with distinct row and column endpoints have total endpoint degree at least six. Then 2(|I|+|J|) is at most 3|S|.

The sum over S of 1/g(i)+1/h(j) equals |I|+|J|: each vertex contributes one when its incident edges are summed. If no edge has both endpoint degrees equal to one, each edge contributes at most 3/2. If such an edge exists, its contribution is two, and every other edge is disjoint from it and has endpoint-degree sum at least four. Each remaining contribution is at most 4/3. Thus 3(|I|+|J|) is at most 4|S|+2; the hypothesis |I|+|J| at least six yields the same two-thirds bound.

**Theorem 1.2 (Lower bound for landmark cardinality).**

$$\forall n \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall S \in \operatorname{Finset}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right)\right)\right),\; \operatorname{IsWeakResolving}\left(2, S\right) \Rightarrow \left(4 \le n \Rightarrow \left(n < m \Rightarrow \operatorname{min}\left(\operatorname{natDiv}\left(2 \cdot \left(n + m\right) + 2, 3\right), 2 \cdot n - 2\right) \le \operatorname{card}\left(S\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionLower.lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of natural numbers n and m with 4 <= n < m, every weak two-resolving landmark set S has cardinality at least min(ceil(2(n+m)/3),2n-2). Here natDiv(a,b) denotes natural number division, and the ceiling equals natDiv(2(n+m)+2,3). An empty row forces at least two landmarks in every other row. An empty column forces at least two landmarks in every other column. If every row and column is occupied, the disjoint-landmark degree constraint and reciprocal-degree charging give 3|S| >= 2(n+m).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionLower.bipartite_degree_charging`
- Truth anchor: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionLower.lower_bound`
- Dependency: [D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore](HammingWeakTwoMetricDimensionCore.md)
