# Exact distances after an involutive matching extension

## Abstract

Finite extension walks reduce to base walks with at most one matching step.

Let G be any simple graph and e a graph automorphism satisfying e(e(u))=u. The extension is the union of G with the undirected loop-free relation joining u to e(u). No finiteness is needed for the walk normal form. For the distance formula G is connected.

**Theorem 1.1 (A native walk normal form).**

$$\forall p \in \operatorname{Walk}\left(\operatorname{extension}\left(e\right), u, v\right),\; \left(\exists q \in \operatorname{Walk}\left(G, u, v\right),\; \operatorname{length}\left(q\right) \le \operatorname{length}\left(p\right)\right) \lor \left(\exists q \in \operatorname{Walk}\left(G, \operatorname{apply}\left(e, u\right), v\right),\; \operatorname{add}\left(\operatorname{length}\left(q\right), 1\right) \le \operatorname{length}\left(p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/InvolutiveMatchingDistance.walk_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induct on the actual extension walk. A base edge is transported through e when necessary. A matching edge toggles the normal form, and two matching steps cancel by involutivity. The resulting base walk never uses more edges than the original walk, counting the possible matching step.

**Theorem 1.2 (The exact minimum formula).**

$$\forall u \in V,\; \forall v \in V,\; \operatorname{dist}\left(\operatorname{extension}\left(e\right), u, v\right) = \operatorname{min}\left(\operatorname{dist}\left(G, u, v\right), \operatorname{add}\left(1, \operatorname{dist}\left(G, \operatorname{apply}\left(e, u\right), v\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/InvolutiveMatchingDistance.distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Base geodesics give both upper bounds, inserting one matching edge for the second bound. Apply the normal form to an extension geodesic to obtain the reverse bound. Fixed points of e cause no difficulty because their extra matching step cannot improve the base distance.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/InvolutiveMatchingDistance.distance`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/InvolutiveMatchingDistance.walk_normal_form`
