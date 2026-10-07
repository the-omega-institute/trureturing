# Greedy Coloring and Vertex Extensions

## Abstract

Greedy ordering colors a connected subcubic graph with a low-degree vertex; compatible colorings also extend across a vertex or glue along a cut.

A coloring with n colors assigns an element of Fin n to each vertex and gives different colors to adjacent vertices. Degree counts neighbors, not an average over vertices. Induce(G,S) denotes the graph induced on S; sets and finite sets are interpreted as vertex subsets when used in this notation.

**Theorem 1.1 (A Low-Degree Vertex in a Connected Subcubic Graph).**

$$\forall V \in \mathrm{Type},\; [\mathrm{Fintype}\left(V\right)] \forall G \in \mathrm{SimpleGraph}\left(V\right),\; [\mathrm{DecidableRel}\left(\mathrm{Adj}\left(G\right)\right)] (\mathrm{Connected}\left(G\right) \land \left(\left(\forall x \in V,\; \mathrm{degree}\left(G, x\right) \le 3\right) \land \left(\exists x \in V,\; \mathrm{degree}\left(G, x\right) < 3\right)\right)) \Rightarrow (\mathrm{Colorable}\left(G, 3\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Brooks/Coloring.connected_colorable_three_of_exists_degree_lt` (`✓ std3`). ∎

*Citation.* Juan Pablo Traverso Gianini (2026). *BrooksSubcubic: finite subcubic four-clique-free graph coloring*. URL: <https://github.com/Vilin97/lean-pool/tree/91c154506e3d08a1a25e4966c22c99212bf9df54/LeanPool/BrooksSubcubic>.

*Commentary.*

Let G be a simple graph on a finite vertex type, with decidable adjacency. If G is connected, every vertex has degree at most three, and some vertex has degree below three, then G is three-colorable. Order vertices by decreasing distance from the chosen low-degree vertex, with an injective tie-breaker. Every other vertex has a closer neighbor still to be colored, so fewer than three already colored neighbors restrict its choice. The root also has fewer than three neighbors. Connectedness includes nonemptiness; the empty graph is not an instance of these premises.

**Theorem 1.2 (Glue Two Three-Colorings at a Vertex).**

$$\forall V \in \mathrm{Type},\; [\mathrm{Fintype}\left(V\right)] [\mathrm{DecidableEq}\left(V\right)] \forall G \in \mathrm{SimpleGraph}\left(V\right),\; \forall A \in \mathrm{Finset}\left(V\right),\; \forall B \in \mathrm{Finset}\left(V\right),\; \forall x \in V,\; (\mathrm{Union}\left(A, B\right) = \mathrm{Univ}\left(V\right) \land \left(\mathrm{Mem}\left(x, A\right) \land \left(\mathrm{Mem}\left(x, B\right) \land \left(\left(\forall u \in V,\; \forall w \in V,\; (\mathrm{Mem}\left(u, A\right) \land \left(\mathrm{Mem}\left(w, B\right) \land \left(u \ne x \land w \ne x\right)\right)) \Rightarrow (\neg (\mathrm{Adj}\left(G, u, w\right)))\right) \land \left(\mathrm{Colorable}\left(\mathrm{Induce}\left(G, A\right), 3\right) \land \mathrm{Colorable}\left(\mathrm{Induce}\left(G, B\right), 3\right)\right)\right)\right)\right)) \Rightarrow (\mathrm{Colorable}\left(G, 3\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Brooks/Coloring.colorable_glue_at_vertex` (`✓ std3`). ∎

*Citation.* Juan Pablo Traverso Gianini (2026). *BrooksSubcubic: finite subcubic four-clique-free graph coloring*. URL: <https://github.com/Vilin97/lean-pool/tree/91c154506e3d08a1a25e4966c22c99212bf9df54/LeanPool/BrooksSubcubic>.

*Commentary.*

For a finite vertex type with decidable equality, let A and B cover all vertices and let x belong to both. Suppose no edge joins a vertex of A other than x to a vertex of B other than x. Three-colorings of G[A] and G[B] then give a three-coloring of G. Permute the colors on B to agree at x, and use the A-coloring wherever A applies. The assumptions do not require connectedness or assert that A and B intersect only at x.

**Theorem 1.3 (Extend a Coloring over One Low-Degree Vertex).**

$$\forall V \in \mathrm{Type},\; \forall G \in \mathrm{SimpleGraph}\left(V\right),\; \forall x \in V,\; \forall n \in \mathrm{Nat},\; [\mathrm{Fintype}\left(\mathrm{neighborSet}\left(G, x\right)\right)] (\mathrm{Colorable}\left(\mathrm{Induce}\left(G, \mathrm{Compl}\left(\mathrm{Singleton}\left(x\right)\right)\right), n\right) \land \mathrm{degree}\left(G, x\right) < n) \Rightarrow (\mathrm{Colorable}\left(G, n\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Brooks/Coloring.of_induce_compl_singleton` (`✓ std3`). ∎

*Citation.* Brian Rabern (2026). *BrooksLean: low-degree vertex coloring extension*. URL: <https://github.com/brianrabern/BrooksLean/tree/1d990050d881327fc79dd51e82ba4449b4e2467d>.

*Commentary.*

Let v be a vertex of any simple graph, and assume only that its neighbor set is finite. If deleting v leaves an n-colorable graph and v has fewer than n neighbors, extend the coloring by choosing a color absent from those neighbors. The entire vertex type need not be finite or connected. The strict degree bound forces n to be positive; no extra positive-color premise is imposed.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Brooks/Coloring.colorable_glue_at_vertex`
- Truth anchor: `D5/S3/Combinatorics/Graph/Brooks/Coloring.connected_colorable_three_of_exists_degree_lt`
- Truth anchor: `D5/S3/Combinatorics/Graph/Brooks/Coloring.of_induce_compl_singleton`
