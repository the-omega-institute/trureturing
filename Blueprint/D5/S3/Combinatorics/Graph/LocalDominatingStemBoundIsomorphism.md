# The one-copy hub isomorphism

## Abstract

For a stem with a unique leaf, the original graph is exactly its one-copy hub graph up to vertex labels.

**Definition 1.1 (Restoring the original vertex labels).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundIsomorphism.oneCopyMap`

*Formalization.* `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundIsomorphism.oneCopyMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite vertex type V, simple graph G, and v,w∈V, the map from (Fin(1)×remaining(G,v))⊕Fin(2) to V sends (i,x) to x, the right vertex 0 to v, and the right vertex 1 to w.

**Definition 1.2 (The one-copy graph isomorphism).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundIsomorphism.oneCopyIso`

*Formalization.* `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundIsomorphism.oneCopyIso` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite V, graph G, and v,w∈V, suppose leafNeighbors(G,v)={w}. Write H for G induced on remaining(G,v), and U for the residual neighbors of v. Restoring the vertex labels gives an isomorphism from replicated(H,U,1) to G. Residual vertices cannot equal v or w; the unique leaf w has no neighbor other than v. All other adjacencies are exactly the original adjacencies retained in H or incident to v.

**Theorem 1.3 (Preservation of the global average).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundIsomorphism.one_copy_avd`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundIsomorphism.one_copy_avd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite V, graph G, and v,w∈V with leafNeighbors(G,v)={w}, avd(replicated(residualGraph(G,v),residualNeighbors(G,v),1))=avd(G). A graph isomorphism bijects dominating sets and preserves their cardinalities.

**Theorem 1.4 (Global equality from the replicated graph).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundIsomorphism.global_equality_from_replication`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundIsomorphism.global_equality_from_replication` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite V, graph G, and v∈V, suppose leafCount(G,v)=1, partialDomSets(G,v)=residualDomSets(G,v), and the mean size of the residual dominating sets equals 2|remaining(G,v)|/3. Then avd(G)=2|V|/3. The one-copy average has equal counting bases and both residual means equal 2h/3. Its exact formula reduces to 2(h+2)/3, where h is the residual order; the graph isomorphism transfers this equality to G.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundIsomorphism.global_equality_from_replication`
- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundIsomorphism.oneCopyIso`
- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundIsomorphism.oneCopyMap`
- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundIsomorphism.one_copy_avd`
- Dependency: [D5/S3/Combinatorics/Graph/LocalDominatingStemBoundResidual](LocalDominatingStemBoundResidual.md)
