# A nearly empty Cartesian layer

## Abstract

Deleting a vertex permits a maximum-degree coloring, which limits one row of a maximal independent set to a singleton.

**Theorem 1.1 (The connected nearly-empty-layer bound).**

$$\forall V \in \mathrm{Type},\; [\operatorname{Fintype}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{Connected}\left(G\right) \Rightarrow \left(\exists I \in \operatorname{Finset}\left(\operatorname{Prod}\left(V, V\right)\right),\; \operatorname{MaximalIndepSet}\left(\operatorname{boxProd}\left(G, G\right), I\right) \land \operatorname{card}\left(I\right) \le \left(\operatorname{FintypeCard}\left(V\right) - 1\right) \cdot \operatorname{indepNum}\left(G\right) + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/NearEmptyLayer.exists_maximalIndepSet_near_empty_layer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Juan Pablo Traverso Gianini (2026). *BrooksSubcubic: finite subcubic four-clique-free graph coloring*. URL: <https://github.com/Vilin97/lean-pool/tree/91c154506e3d08a1a25e4966c22c99212bf9df54/LeanPool/BrooksSubcubic>.

*Commentary.*

Let G be a finite connected simple graph. Order vertices by decreasing distance from a chosen root, breaking ties injectively. In the graph with that root deleted, each vertex has an original neighbor that is either deleted or later in the order. Greedy coloring therefore uses at most the maximum degree. Assign each color to a different neighbor of a maximum-degree vertex. The resulting independent set dominates its Cartesian row except at the deleted second coordinate. A maximal extension meets that row at most once; every other row contributes at most alpha(G). Maximal means inclusion-maximal, and every finite connected graph, including the singleton, remains in scope.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Products/NearEmptyLayer.exists_maximalIndepSet_near_empty_layer`
- Dependency: [D5/S3/Combinatorics/Graph/Brooks/Coloring](../Brooks/Coloring.md)
- Dependency: [D5/S3/Combinatorics/Graph/Products/EmptyLayer](EmptyLayer.md)
