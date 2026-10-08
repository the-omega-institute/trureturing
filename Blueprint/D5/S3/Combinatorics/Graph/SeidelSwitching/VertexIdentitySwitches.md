# Every vertex an identity Seidel switch

## Abstract

A finite nonempty simple graph has every vertex as an identity Seidel switch if and only if it has one vertex. Edge-count preservation forces regularity, and switching at a vertex changes the degree of each other vertex by one.

**Definition 1.1 (Seidel switching across a subset).**

$$\forall (V : Type), \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (S : \operatorname{Set}\left(V\right)), \forall (x : V), \forall (y : V), (\operatorname{SimpleGraph.Adj}\left(\operatorname{seidelSwitch}\left(G, S\right), x, y\right)) \Leftrightarrow ((x \ne y) \land ((\operatorname{SimpleGraph.Adj}\left(G, x, y\right)) \Leftrightarrow ((x \in S) \Leftrightarrow (y \in S))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/SeidelSwitching/VertexIdentitySwitches.seidelSwitch` (`✓ std3`).

*Citation.* Severino V. Gervacio (2026). *On identity Seidel switches*. URL: <https://arxiv.org/abs/2601.04530v1>.

*Commentary.*

Theorem 2.6, page 6: "Let G be a graph and S a non-empty subset of V(G). Then S(G) is obtained from G by deleting all edges xy with x ∈ S and y ∈ V(G) ∖ S, and adding all non-edges xy with x ∈ S and y ∈ V(G) ∖ S. Edges with both ends in S or both ends in V(G) ∖ S remain unchanged." The displayed adjacency relation is the subset switch: different membership in S negates G.Adj, equal membership preserves it, and x ≠ y excludes loops. For the empty subset the relation is G.Adj, agreeing with the source's empty-switch convention on page 6. Section 2.1, page 3: "Let G be a graph and v ∈ V(G). The Seidel switch of G by v, denoted v(G), is the graph obtained from G by deleting all edges vy where y ∈ N_G(v) and adding all edges vz where z ∈ V(G) ∖ N_G(v) and z ≠ v. In other words, we complement the adjacency relation between v and the rest of the vertex set, while leaving all other adjacencies unchanged." Taking S = {v} gives this vertex switch.

**Definition 1.2 (Vertex identity Seidel switch).**

$$\forall (V : Type), \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (x : V), (\operatorname{IsVertexISS}\left(G, x\right)) \Leftrightarrow (\operatorname{Nonempty}\left(\operatorname{SimpleGraph.Iso}\left(\operatorname{seidelSwitch}\left(G, \{x\}\right), G\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/SeidelSwitching/VertexIdentitySwitches.IsVertexISS` (`✓ std3`).

*Citation.* Severino V. Gervacio (2026). *On identity Seidel switches*. URL: <https://arxiv.org/abs/2601.04530v1>.

*Commentary.*

Definition 4.1, page 8: "Let G be a graph. A subset S ⊆ V(G) is called an identity Seidel switch (abbreviated ISS) if S(G) ≅ G." Section 4, page 9: "We say that {x} is a vertex-ISS if {x} is an ISS, and that {x, y} is an edge-ISS if {x, y} is an ISS and xy ∈ E(G)." Nonempty expresses existence of a graph isomorphism; the cut is precisely the singleton {x}.

**Definition 1.3 (The complete characterization).**

$$(\operatorname{claim}) \Leftrightarrow (\forall (V : Type), [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] [\operatorname{Nonempty}\left(V\right)] \forall (G : \operatorname{SimpleGraph}\left(V\right)), (\forall (x : V), \operatorname{IsVertexISS}\left(G, x\right)) \Leftrightarrow (\operatorname{Fintype.card}\left(V\right) = 1))$$

*Formalization.* `D5/S3/Combinatorics/Graph/SeidelSwitching/VertexIdentitySwitches.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Severino V. Gervacio (2026). *On identity Seidel switches*. URL: <https://arxiv.org/abs/2601.04530v1>.

*Commentary.*

Problem 6.1, page 13: "Characterize graphs G for which every vertex is a vertex-ISS. Lemma 4.4 gives a necessary condition in terms of the minimum and maximum degree; can this be strengthened to a complete characterization?" Section 2, page 3: "Throughout, a graph G is an ordered pair G = ⟨V(G), E(G)⟩ where V(G) is a non-empty finite set whose elements are called vertices and E(G) is a set of 2-element subsets of V(G) called edges." V is any Type with Fintype, DecidableEq and Nonempty instances, and G is any SimpleGraph on V. The answer is that its cardinality equals one. There is no connectivity, regularity, or adjacency-decidability hypothesis.

**Theorem 1.4 (Exactly the one-vertex graph).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SeidelSwitching/VertexIdentitySwitches.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Severino V. Gervacio (2026). *On identity Seidel switches*. URL: <https://arxiv.org/abs/2601.04530v1>.

*Commentary.*

Switching at v leaves the nonincident edges unchanged. The old and new incident-edge counts are the two complementary neighbour counts, whose sum is card(V)−1. Hence the new edge count plus twice degree(v) equals the old edge count plus card(V)−1. An identity switch preserves the edge count; if every vertex is an identity switch, twice every degree equals card(V)−1. If card(V)>1 this forces a positive common degree. Choose a neighbour w of v. Switching at v lowers the degree of w by one, while the isomorphism would send w to a vertex with the original common degree: contradiction. At order one the adjacency relation is empty and the switch equals G. More generally, at a vertex y, switching across S preserves same-side neighbours and exchanges crossing neighbours with crossing non-neighbours. The new degree plus twice the old crossing-neighbour count equals the old degree plus the number of vertices on the opposite side. This identity includes empty and full cuts. Natural subtraction denotes truncated subtraction. The literal conclusion of Lemma 4.4 includes a same-vertex case in the one-vertex graph; an adjacency assertion there needs distinct vertices. The characterization does not answer Problems 6.2–6.4.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/SeidelSwitching/VertexIdentitySwitches.IsVertexISS`
- Truth anchor: `D5/S3/Combinatorics/Graph/SeidelSwitching/VertexIdentitySwitches.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/SeidelSwitching/VertexIdentitySwitches.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/SeidelSwitching/VertexIdentitySwitches.seidelSwitch`
