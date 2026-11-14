# Shortest toggle words between finite order-convex sets

## Abstract

Finite order-convex sets have guarded toggle paths of Hamming length in every poset.

Let P be an arbitrary partially ordered set. A subset is order-convex when it contains every ambient point between any two of its members. The operation RowmotionEndpointTransport.toggle flips membership at x only when the resulting set is order-convex, and otherwise leaves the set fixed. All intervals and legality tests below use the original order on P.

**Theorem 1.1 (A word toggling each differing point once).**

$$\forall P \in Type,\; [\operatorname{PartialOrder}\left(P\right)], \forall s \in \operatorname{Finset}\left(P\right),\; \forall t \in \operatorname{Finset}\left(P\right),\; (\operatorname{OrdConnected}\left(\operatorname{coe}\left(s\right)\right)) \Rightarrow ((\operatorname{OrdConnected}\left(\operatorname{coe}\left(t\right)\right)) \Rightarrow (\exists w \in \operatorname{List}\left(P\right),\; (\operatorname{Nodup}\left(w\right)) \land ((\operatorname{toFinset}\left(w\right) = \operatorname{SymmDiff}\left(s, t\right)) \land ((\operatorname{length}\left(w\right) = \operatorname{card}\left(\operatorname{SymmDiff}\left(s, t\right)\right)) \land (\operatorname{foldl}\left((A, x) \mapsto \operatorname{toggle}\left(x, A\right), \operatorname{coe}\left(s\right), w\right) = \operatorname{coe}\left(t\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/RowmotionConvexGeodesic.exists_toggle_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite order-convex subsets s and t of P, there is a list w with no repetitions whose elements are exactly the symmetric difference of s and t. Its length is the cardinality of that symmetric difference. Starting from s, applying the original guarded toggle successively along w yields t. No finiteness, local finiteness or inhabitance assumption is imposed on P. Empty, disjoint and nested endpoints are included.

To contract a finite order-convex set A onto an order-convex subset K, choose a point z in A outside K. Finiteness of A supplies a minimal point a of A below z and a maximal point b of A above z. If both a and b belonged to K, convexity of K would force z into K. Thus at least one of these extreme points lies outside K. Deleting a minimal or maximal point preserves ambient order-convexity. Repeating this step gives a deletion word from A to K, with each point of A minus K used once. Every deletion is reversible by the same guarded toggle.

Apply the contraction to s and t with K equal to their intersection. Follow the deletion word from s to K, then the reverse of the deletion word from t to K. The two lists have disjoint supports, namely s minus t and t minus s, so their concatenation has no repetitions and support s symmetric difference t. This realizes the Hamming lower bound expressed by HereditaryFlip.Metric.walk_lower_bound: each differing coordinate must change at least once along any one-coordinate walk. The contraction argument uses convexity of the retained subset; arbitrary subsets of an order-convex set need not be order-convex.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/RowmotionConvexGeodesic.exists_toggle_word`
- Dependency: [D5/S3/Combinatorics/Geometry/RowmotionEndpointTransport](RowmotionEndpointTransport.md)
