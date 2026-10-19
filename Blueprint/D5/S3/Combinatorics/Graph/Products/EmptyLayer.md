# An empty Cartesian layer

## Abstract

A coloring with at most the maximum degree permits a maximal independent set to omit an entire Cartesian layer.

**Theorem 1.1 (The chromatic empty-layer bound).**

$$\forall V \in \mathrm{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{Nonempty}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \operatorname{chromaticNumber}\left(G\right) \le \operatorname{maxDegree}\left(G\right) \Rightarrow \left(\exists I \in \operatorname{Finset}\left(\operatorname{Prod}\left(V, V\right)\right),\; \operatorname{MaximalIndepSet}\left(\operatorname{boxProd}\left(G, G\right), I\right) \land \operatorname{card}\left(I\right) \le \left(\operatorname{FintypeCard}\left(V\right) - 1\right) \cdot \operatorname{indepNum}\left(G\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/EmptyLayer.exists_maximalIndepSet_empty_layer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be any finite nonempty simple graph with chromatic number at most maximum degree. Choose a proper coloring with that many colors and inject the colors into the neighbors of a maximum-degree vertex v. The pairs (neighbor(color(y)),y) form an independent set that dominates the entire row with first coordinate v. Extend this prescribed set to an inclusion-maximal independent set. It avoids that row, so the other |V|-1 rows contribute at most (|V|-1) alpha(G). No regularity or connectedness hypothesis is imposed.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Products/EmptyLayer.exists_maximalIndepSet_empty_layer`
- Dependency: [D5/S3/Combinatorics/Graph/Products/CayleyIndependence](CayleyIndependence.md)
