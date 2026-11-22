# Capacity bounds for ranked bipartite graphs

## Abstract

Use degree capacities to bound the charge in an ordered bipartite graph.

**Theorem 1.1 (Summed capacity deficits bound the odd-rank edge charge).**

$$\operatorname{CapacityDeficitSum}\left(R\right) \le \operatorname{OddEdgeCharge}\left(e\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/RankCuts/RankedBipartiteCapacity.paid_edges_ge_rank_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use two copies of a finite vertex set with natural-number ranks and natural edge multiplicities e. Fix a vertex t. Each positive entry from an ordinary row is diagonal or goes to a strictly higher rank. Every ordinary row and column has total multiplicity between one and k.

Let R be a finite set of odd ranks below the rank of t. At a rank r in R, subtract k times the number of vertices strictly below r and the actual weight from row t into columns at or below r from the number of vertices at or below r. Also subtract k times the number of ordinary vertices strictly above r and the actual weight from ordinary rows at or above r into column t from the number of ordinary vertices at or above r. Take the maximum of zero and these two differences. CapacityDeficitSum sums the resulting value over R.

OddEdgeCharge sums e over edges from ordinary odd-rank rows to odd-rank columns. In the first count, positive entries reaching the lower prefix from ordinary rows at or above its boundary can only use its diagonal. In the second count, positive entries leaving the upper suffix for columns at or below its boundary also use its diagonal. Each layer has a disjoint set of diagonal entries. Their contributions therefore sum within the charge.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/RankCuts/RankedBipartiteCapacity.paid_edges_ge_rank_capacity`
