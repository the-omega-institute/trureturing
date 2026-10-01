# Condensation need not preserve LC-equivalence

## Abstract

Two connected six-vertex graphs are related by local complementations and satisfy the bound of at most one outside neighbour for every vertex of the condensation set in both graphs, but their condensed graphs are not LC-equivalent. This refutes Conjecture 16 of Vandré, de Jong, Hahn, Burchardt, Gühne and Pappa.

**Definition 1.1 (Condensed graph).**

$$\forall V \in \operatorname{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall C \in \operatorname{Finset}\left(V\right),\; \begin{aligned}\operatorname{condense}\left(G, C\right): \operatorname{SimpleGraph}\left(\operatorname{Option}\left(\{v: V \mid \neg (v \in C)\}\right)\right)\\\operatorname{Adj}\left(\operatorname{condense}\left(G, C\right), \operatorname{none}, \operatorname{none}\right) \Leftrightarrow (\operatorname{False})\\\forall i \in \{v: V \mid \neg (v \in C)\},\; \forall j \in \{v: V \mid \neg (v \in C)\},\; \operatorname{Adj}\left(\operatorname{condense}\left(G, C\right), \operatorname{some}\left(i\right), \operatorname{some}\left(j\right)\right) \Leftrightarrow (\operatorname{Adj}\left(G, \operatorname{val}\left(i\right), \operatorname{val}\left(j\right)\right))\\\forall i \in \{v: V \mid \neg (v \in C)\},\; \operatorname{Adj}\left(\operatorname{condense}\left(G, C\right), \operatorname{some}\left(i\right), \operatorname{none}\right) \Leftrightarrow (\exists s \in V,\; (s \in C) \land (\operatorname{Adj}\left(G, \operatorname{val}\left(i\right), s\right)))\\\forall i \in \{v: V \mid \neg (v \in C)\},\; \operatorname{Adj}\left(\operatorname{condense}\left(G, C\right), \operatorname{none}, \operatorname{some}\left(i\right)\right) \Leftrightarrow (\exists s \in V,\; (s \in C) \land (\operatorname{Adj}\left(G, \operatorname{val}\left(i\right), s\right)))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphCondensationLCRefutation.condense` (`✓ std3`).

*Citation.* Lina Vandré; Jarn de Jong; Frederik Hahn; Adam Burchardt; Otfried Gühne; Anna Pappa (2024). *Distinguishing Graph States by the Properties of Their Marginals*. DOI: [10.48550/arXiv.2406.09956](https://doi.org/10.48550/arXiv.2406.09956). URL: <https://arxiv.org/abs/2406.09956v2>.

*Commentary.*

Definition 13 (arXiv:2406.09956v2, p. 12): “Consider a graph G = (V, E) and a set C ⊆ V. The condensed graph G_C = (V_C, E_C) consists of the node set V_C = {c} ∪ (V \ C) and edge set E_C defined in the following way: (i, j) ∈ E_C if either i, j ∈ V \ C and (i, j) ∈ E, or j = c and there exists s ∈ C such that (i, s) ∈ E.” The fresh vertex c is none; an outside vertex is some(i), where i is a subtype element with val(i) ∉ C. The undirected adjacency is symmetrized, and none is not adjacent to itself. The graph type and the four adjacency cases below are the defining expression.

**Definition 1.2 (Finite sequences of local complementations).**

$$\forall V \in \operatorname{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall H \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{LCEquivalent}\left(G, H\right) \Leftrightarrow (\exists s \in \operatorname{List}\left(V\right),\; H = \operatorname{lcSeq}\left(G, s\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphCondensationLCRefutation.LCEquivalent` (`✓ std3`).

*Citation.* Lina Vandré; Jarn de Jong; Frederik Hahn; Adam Burchardt; Otfried Gühne; Anna Pappa (2024). *Distinguishing Graph States by the Properties of Their Marginals*. DOI: [10.48550/arXiv.2406.09956](https://doi.org/10.48550/arXiv.2406.09956). URL: <https://arxiv.org/abs/2406.09956v2>.

*Commentary.*

LC-equivalence is existence of a finite list s of vertices such that H = lcSeq(G, s). Local complementation complements the edges between the selected vertex's neighbours and preserves all other edges. The reused lcSeq applies these operations in list order. The paper states (p. 5): “There is a one-to-one correspondence between the local complementation orbit of a given graph and the orbit under local Clifford operations of the corresponding graph state.” Definition 4 (pp. 4–5) gives the local complementation formula; the correspondence cites Van den Nest, Dehaene and De Moor (2004).

**Definition 1.3 (Conjecture 16).**

$$claim \Leftrightarrow (\forall (V: \operatorname{Type}) [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall H \in \operatorname{SimpleGraph}\left(V\right),\; \forall C \in \operatorname{Finset}\left(V\right),\; (\operatorname{Connected}\left(G\right)) \Rightarrow ((\operatorname{Connected}\left(H\right)) \Rightarrow ((\forall s \in V,\; (s \in C) \Rightarrow (\operatorname{card}\left(\operatorname{filter}\left(\operatorname{univ}, i \mapsto ((\neg (i \in C)) \land (\operatorname{Adj}\left(G, s, i\right)))\right)\right) \le 1)) \Rightarrow ((\forall s \in V,\; (s \in C) \Rightarrow (\operatorname{card}\left(\operatorname{filter}\left(\operatorname{univ}, i \mapsto ((\neg (i \in C)) \land (\operatorname{Adj}\left(H, s, i\right)))\right)\right) \le 1)) \Rightarrow ((\operatorname{LCEquivalent}\left(G, H\right)) \Rightarrow (\operatorname{LCEquivalent}\left(\operatorname{condense}\left(G, C\right), \operatorname{condense}\left(H, C\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphCondensationLCRefutation.claim` (`✓ std3`).

*Citation.* Lina Vandré; Jarn de Jong; Frederik Hahn; Adam Burchardt; Otfried Gühne; Anna Pappa (2024). *Distinguishing Graph States by the Properties of Their Marginals*. DOI: [10.48550/arXiv.2406.09956](https://doi.org/10.48550/arXiv.2406.09956). URL: <https://arxiv.org/abs/2406.09956v2>.

*Commentary.*

Conjecture 16 (arXiv:2406.09956v2, p. 13): “Given two graphs G and G′ and a condensation set C such that each node in C is connected to at most one node in the neighborhood in V \ C. If G and G′ are LC-equivalent, it follows that G_c and G′_c are LC-equivalent.” V is any finite labelled vertex type with decidable equality, G and H encode G and G′, and C is a finset. The bracketed [Fintype V] and [DecidableEq V] terms are the anonymous Lean typeclass assumptions. Both graphs are connected, as the paper assumes for its simple graphs. The outside-neighbour bound is required in both graphs: the cardinality of {i in V | i ∉ C and Adj(G, s, i)} is at most one for every s ∈ C, and likewise for H. The function filter selects precisely these vertices from univ; card is finset cardinality. This reading meets the degree condition on both sides.

**Theorem 1.4 (Six vertices refute the conjecture).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GraphCondensationLCRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lina Vandré; Jarn de Jong; Frederik Hahn; Adam Burchardt; Otfried Gühne; Anna Pappa (2024). *Distinguishing Graph States by the Properties of Their Marginals*. DOI: [10.48550/arXiv.2406.09956](https://doi.org/10.48550/arXiv.2406.09956). URL: <https://arxiv.org/abs/2406.09956v2>.

*Commentary.*

On Fin(6), take C = {0, 1, 2}, E(G) = {01, 02, 05, 14, 23} and E(H) = {05, 14, 23, 35, 45}. Both graphs are connected and each vertex of C has exactly one outside neighbour. Complementing at 0, 1, 2, 3, 4, 5 in order maps G to H. Condensation gives Mathlib's star graph with centre none and leaves 3, 4, 5, and the diamond with edges {c3, c4, c5, 35, 45}. The family consisting of the complete graph and every star is closed under local complementation: at a star's centre it gives the complete graph, at a leaf it preserves the star, and at a vertex of the complete graph it gives the star centred there. Induction over the list of operations keeps the condensed first graph in this family. The diamond is neither complete nor any of the four stars, as specific adjacency comparisons show, so it cannot be reached. On four vertices the family's graphs have three or six edges, while the diamond has five.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/GraphCondensationLCRefutation.LCEquivalent`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphCondensationLCRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphCondensationLCRefutation.condense`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphCondensationLCRefutation.result`
- Dependency: [D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph](GraphStateMonogamyForbiddenSubgraph.md)
