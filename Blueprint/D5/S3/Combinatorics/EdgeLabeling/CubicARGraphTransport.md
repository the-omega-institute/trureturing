# Transport of additive rigidity

## Abstract

AR-labelings pull back along graph isomorphisms.

**Theorem 1.1 (Pullback of an AR-labeling).**

$$\operatorname{Isomorphic}\left(G, H\right) \land \operatorname{IsARGraph}\left(H\right) \implies \operatorname{IsARGraph}\left(G\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphTransport.ar_graph_of_iso` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G and H be simple graphs on finite vertex types. If they are isomorphic and H has an AR-labeling onto the integers from one through its edge count, then G has such an AR-labeling. Pull back the label of an edge along the isomorphism-induced edge map. This map is a bijection of edge sets and preserves incidence. It also sends distinct subsets of an incidence set to distinct subsets while preserving their label sums.

## References

- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphTransport.ar_graph_of_iso`
- Dependency: [D5/S3/Combinatorics/EdgeLabeling/CubicARGraphDefs](CubicARGraphDefs.md)
