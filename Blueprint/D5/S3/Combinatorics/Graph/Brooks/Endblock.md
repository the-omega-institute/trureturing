# A Good Triple from a Two-Vertex Cut

## Abstract

In a finite cubic graph whose every vertex deletion is connected, a separating pair with nonempty complement yields two nonadjacent neighbors whose deletion remains connected.

**Theorem 1.1 (The Endblock Case).**

$$\forall V \in \mathrm{Type},\; [\mathrm{Fintype}\left(V\right)] \forall G \in \mathrm{SimpleGraph}\left(V\right),\; [\mathrm{DecidableRel}\left(\mathrm{Adj}\left(G\right)\right)] \forall x \in V,\; \forall y \in V,\; \forall w \in V,\; (\left(\forall z \in V,\; \mathrm{degree}\left(G, z\right) = 3\right) \land \left(\left(\forall z \in V,\; \mathrm{Connected}\left(\mathrm{Induce}\left(G, \mathrm{Compl}\left(\mathrm{Singleton}\left(z\right)\right)\right)\right)\right) \land \left(x \ne y \land \left(\neg (\mathrm{Mem}\left(w, \mathrm{Pair}\left(x, y\right)\right)) \land \neg (\mathrm{Connected}\left(\mathrm{Induce}\left(G, \mathrm{Compl}\left(\mathrm{Pair}\left(x, y\right)\right)\right)\right))\right)\right)\right)) \Rightarrow (\exists t \in V,\; \exists a \in V,\; \exists b \in V,\; \mathrm{Adj}\left(G, t, a\right) \land \left(\mathrm{Adj}\left(G, t, b\right) \land \left(a \ne b \land \left(\neg (\mathrm{Adj}\left(G, a, b\right)) \land \mathrm{Connected}\left(\mathrm{Induce}\left(G, \mathrm{Compl}\left(\mathrm{Pair}\left(a, b\right)\right)\right)\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Brooks/Endblock.good_triple_of_two_cut` (`✓ std3`). ∎

*Citation.* Juan Pablo Traverso Gianini (2026). *BrooksSubcubic: finite subcubic four-clique-free graph coloring*. URL: <https://github.com/Vilin97/lean-pool/tree/91c154506e3d08a1a25e4966c22c99212bf9df54/LeanPool/BrooksSubcubic>.

*Commentary.*

Let G be a simple graph on a finite vertex type with decidable adjacency. Every vertex has degree exactly three, and deleting any one vertex leaves a connected graph. Suppose distinct vertices x and y separate the graph when deleted, and specify a vertex w outside that pair. Then there are vertices v, a, and b such that a and b are distinct nonadjacent neighbors of v and deleting a and b leaves a connected graph.

The witness w makes the complement of the separating pair nonempty; disconnectedness alone would also include an empty complement. The hypothesis about every single-vertex deletion explicitly asks for connectedness, including nonemptiness. No separate assumption that G has no four-clique is used in this theorem.

Components after deleting x and y attach to the separating vertices. The degree-three constraint limits the attachment possibilities. Choosing suitable neighbors from the separated components gives a nonadjacent pair, and the endblock argument refines the choice so that its deletion preserves connectedness. This good triple provides the geometric input for the cubic coloring argument; the conclusion here is the triple itself.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Brooks/Endblock.good_triple_of_two_cut`
- Dependency: [D5/S3/Combinatorics/Graph/Brooks/Cuts](Cuts.md)
