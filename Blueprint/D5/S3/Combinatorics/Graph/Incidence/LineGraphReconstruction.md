# Reconstructing vertices from incident edges

## Abstract

A prescribed isomorphism of line graphs determines exactly one isomorphism of their triangle-free roots when every vertex has two distinct neighbors.

**Theorem 1.1 (The unique lift of the supplied edge isomorphism).**

$$\forall u \in \mathrm{Level},\; \forall v \in \mathrm{Level},\; \forall V \in \operatorname{Type}\left(u\right),\; \forall W \in \operatorname{Type}\left(v\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall H \in \operatorname{SimpleGraph}\left(W\right),\; \left(\operatorname{CliqueFree}\left(G, 3\right) \land \left(\operatorname{CliqueFree}\left(H, 3\right) \land \left(\left(\forall x \in V,\; \operatorname{Nontrivial}\left(\operatorname{neighborSet}\left(G, x\right)\right)\right) \land \left(\forall y \in W,\; \operatorname{Nontrivial}\left(\operatorname{neighborSet}\left(H, y\right)\right)\right)\right)\right)\right) \Rightarrow \left(\forall e \in \operatorname{Iso}\left(\operatorname{lineGraph}\left(G\right), \operatorname{lineGraph}\left(H\right)\right),\; \exists f \in \operatorname{Iso}\left(G, H\right),\; \operatorname{lineGraph}\left(f\right) = e \land \left(\forall k \in \operatorname{Iso}\left(G, H\right),\; \operatorname{lineGraph}\left(k\right) = e \Rightarrow k = f\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Incidence/LineGraphReconstruction.exists_unique_line_graph_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V and W range over independent universes, and let G and H be simple graphs. Assume that each graph has no three-vertex clique and that each vertex has at least two distinct neighbors. For every supplied isomorphism e between their line graphs, there exists exactly one graph isomorphism f from G to H whose induced line graph isomorphism equals e. Iso denotes graph isomorphisms, and lineGraph denotes the graph construction and its action on isomorphisms. The formula expands unique existence as existence together with equality of every other lift to f.

Choose two distinct edges incident to a vertex x. Their images intersect at a vertex y. Any third incident edge has an image intersecting both. Restrict these three image edges to their finite endpoint support and apply the intersecting-family classification from DUFStructure. The triangle alternative contradicts the absence of three-vertex cliques. Thus all three images have a common endpoint, which must be y because the first two edges are distinct. This reconstructs the image of the whole incident star at x.

Apply the same construction to the inverse edge isomorphism. The two original incident edges force the two vertex maps to be inverse. Incidence is then preserved in both directions, so the vertex maps preserve adjacency and the induced unordered edge map is exactly e. Any other lift places the image of x on the same two distinct image edges and therefore agrees at every vertex.

The vertex types may be empty or infinite, and the graphs may be disconnected. Only the endpoint support used for each local classification is finite. Choice is used inside the proof. The hypotheses are sufficient; no assertion of sharpness or literature priority is made.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/LineGraphReconstruction.exists_unique_line_graph_lift`
- Dependency: [D5/S3/Combinatorics/Graph/DUFStructure](../DUFStructure.md)
