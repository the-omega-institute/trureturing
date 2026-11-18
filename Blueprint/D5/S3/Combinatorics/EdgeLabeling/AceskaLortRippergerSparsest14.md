# A connected 23-edge DDMOG on fourteen vertices

## Abstract

A connected 14-vertex DDMOG with 23 edges refutes the proposed 24-edge lower bound.

**Definition 1.1 (Incoming label sum minus outgoing label sum).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] \forall D \in \operatorname{Digraph}\left(V\right),\; \forall f \in V \to Int,\; \forall x \in V,\; \operatorname{weight}\left(D, f, x\right) = \sum_{y : V} (\operatorname{if} y \in \{y : V | \operatorname{Digraph}.\operatorname{Adj}\left(D, y, x\right)\} \operatorname{then} f\left(y\right) \operatorname{else} 0) - \sum_{y : V} (\operatorname{if} y \in \{y : V | \operatorname{Digraph}.\operatorname{Adj}\left(D, x, y\right)\} \operatorname{then} f\left(y\right) \operatorname{else} 0)$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/AceskaLortRippergerSparsest14.weight` (`✓ std3`).

*Citation.* Roza Aceska; McKailyn Lort; Allison Ripperger (2026). *Ornaments and Difference Distance Magic Oriented Graphs*. DOI: [10.48550/arXiv.2606.16001](https://doi.org/10.48550/arXiv.2606.16001). URL: <https://arxiv.org/abs/2606.16001v3>.

*Commentary.*

Section 1.1, page 2: “The weight of vertex x is defined [2] as the sum of the vertex labels directed into x minus the sum of vertex labels directed out of x,” followed by wt(x) = ∑_{y∈N⁺(x)} f(y) − ∑_{y∈N⁻(x)} f(y). Page 1: “The in-neighborhood of a vertex v is the set of vertices u ∈ V(D) such that (u,v) ∈ E(D) and is denoted N⁺(v).” The out-neighborhood uses (v,u). Both sums run over the finite vertex type, with zero outside the relevant set. Labels and weights are integers.

**Definition 1.2 (Bijection onto the consecutive integer labels).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] \forall f \in V \to Int,\; (\operatorname{IsConsecutiveLabeling}\left(f\right)) \Leftrightarrow (\operatorname{Set}.\operatorname{BijOn}\left(f, \operatorname{Set}.\operatorname{univ}, \operatorname{Set}.\operatorname{Icc}\left((1 : Int), (\operatorname{Fintype}.\operatorname{card}\left(V\right) : Int)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/AceskaLortRippergerSparsest14.IsConsecutiveLabeling` (`✓ std3`).

*Citation.* Roza Aceska; McKailyn Lort; Allison Ripperger (2026). *Ornaments and Difference Distance Magic Oriented Graphs*. DOI: [10.48550/arXiv.2606.16001](https://doi.org/10.48550/arXiv.2606.16001). URL: <https://arxiv.org/abs/2606.16001v3>.

*Commentary.*

Section 1.1, page 2: “A difference distance magic (DDM) labeling [2] of an oriented graph G⃗ with n vertices is a bijection f: V(G⃗) → {1,2,...,n} where there exists some k ∈ ℕ such that for all x ∈ V(G⃗) wt_f(x)=k; it shows that k=0 for all x ∈ V(G⃗).” This predicate expresses the bijection clause using Set.BijOn. The interval endpoints and the cardinality cast have type Int.

**Definition 1.3 (Consecutive labels with a common natural weight).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] \forall D \in \operatorname{Digraph}\left(V\right),\; \forall f \in V \to Int,\; (\operatorname{IsDDMLabeling}\left(D, f\right)) \Leftrightarrow ((\operatorname{IsConsecutiveLabeling}\left(f\right)) \land (\exists k \in Nat,\; \forall x \in V,\; \operatorname{weight}\left(D, f, x\right) = (k : Int)))$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/AceskaLortRippergerSparsest14.IsDDMLabeling` (`✓ std3`).

*Citation.* Roza Aceska; McKailyn Lort; Allison Ripperger (2026). *Ornaments and Difference Distance Magic Oriented Graphs*. DOI: [10.48550/arXiv.2606.16001](https://doi.org/10.48550/arXiv.2606.16001). URL: <https://arxiv.org/abs/2606.16001v3>.

*Commentary.*

Section 1.1, page 2: “A difference distance magic (DDM) labeling [2] of an oriented graph G⃗ with n vertices is a bijection f: V(G⃗) → {1,2,...,n} where there exists some k ∈ ℕ such that for all x ∈ V(G⃗) wt_f(x)=k; it shows that k=0 for all x ∈ V(G⃗).” The common constant k remains existential and natural; its occurrence in the integer weight equality is coerced to Int.

**Definition 1.4 (Number of directed edges).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] \forall D \in \operatorname{Digraph}\left(V\right),\; \operatorname{edgeCount}\left(D\right) = \operatorname{Fintype}.\operatorname{card}\left(\{e : V \times V // \operatorname{Digraph}.\operatorname{Adj}\left(D, e.1, e.2\right)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/AceskaLortRippergerSparsest14.edgeCount` (`✓ std3`).

*Citation.* Roza Aceska; McKailyn Lort; Allison Ripperger (2026). *Ornaments and Difference Distance Magic Oriented Graphs*. DOI: [10.48550/arXiv.2606.16001](https://doi.org/10.48550/arXiv.2606.16001). URL: <https://arxiv.org/abs/2606.16001v3>.

*Commentary.*

Section 1.1, page 1: “A digraph D is a graph with directed edges: it is defined to be a pair (V,E), consisting of a set of vertices V(D) and a collection of ordered pairs of vertices E(D), called edges.” This cardinality counts ordered adjacent pairs. For an oriented graph there are no loops or opposite arcs, so it also counts the underlying undirected edges.

**Definition 1.5 (The fourteen-vertex minimality conjecture).**

$$(\operatorname{claim}) \Leftrightarrow (\forall D \in \operatorname{Digraph}\left(\operatorname{Fin}\left(14\right)\right),\; \forall f \in \operatorname{Fin}\left(14\right) \to Int,\; (\operatorname{Std}.\operatorname{Asymm}\left(\operatorname{Digraph}.\operatorname{Adj}\left(D\right)\right)) \Rightarrow ((\operatorname{SimpleGraph}.\operatorname{Connected}\left(\operatorname{SimpleGraph}.\operatorname{fromRel}\left((fun (u : \operatorname{Fin}\left(14\right)) \mapsto fun (v : \operatorname{Fin}\left(14\right)) \mapsto (\operatorname{Digraph}.\operatorname{Adj}\left(D, u, v\right)) \lor (\operatorname{Digraph}.\operatorname{Adj}\left(D, v, u\right)))\right)\right)) \Rightarrow ((\operatorname{IsDDMLabeling}\left(D, f\right)) \Rightarrow (24 \le \operatorname{edgeCount}\left(D\right)))))$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/AceskaLortRippergerSparsest14.claim` (`✓ std3`).

*Citation.* Roza Aceska; McKailyn Lort; Allison Ripperger (2026). *Ornaments and Difference Distance Magic Oriented Graphs*. DOI: [10.48550/arXiv.2606.16001](https://doi.org/10.48550/arXiv.2606.16001). URL: <https://arxiv.org/abs/2606.16001v3>.

*Commentary.*

Conclusion, page 25: “Another question we have encountered as we were writing this paper is related to the minimal number of edges a connected DDMOG with n vertices must have: What is the sparsest connected DDMOG with n vertices in terms of edges? When observing the DDMOG with 14 vertices in Figure 6, we conjecture that it is the sparsest DDMOG with 14 vertices.” Remark 2, page 9, counts 24 edges in Figure 6. Fin 14 indexes the vertices from zero; Std.Asymm excludes loops and opposite arcs. SimpleGraph.fromRel gives the undirected graph, and Connected is its usual connectedness. The asserted lower bound is 24 for every consecutive DDM labeling.

**Theorem 1.6 (The 24-edge lower bound is false).**

$$\neg (\forall D \in \operatorname{Digraph}\left(\operatorname{Fin}\left(14\right)\right),\; \forall f \in \operatorname{Fin}\left(14\right) \to Int,\; (\operatorname{Std}.\operatorname{Asymm}\left(\operatorname{Digraph}.\operatorname{Adj}\left(D\right)\right)) \Rightarrow ((\operatorname{SimpleGraph}.\operatorname{Connected}\left(\operatorname{SimpleGraph}.\operatorname{fromRel}\left((fun (u : \operatorname{Fin}\left(14\right)) \mapsto fun (v : \operatorname{Fin}\left(14\right)) \mapsto (\operatorname{Digraph}.\operatorname{Adj}\left(D, u, v\right)) \lor (\operatorname{Digraph}.\operatorname{Adj}\left(D, v, u\right)))\right)\right)) \Rightarrow ((\operatorname{IsDDMLabeling}\left(D, f\right)) \Rightarrow (24 \le \operatorname{edgeCount}\left(D\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/AceskaLortRippergerSparsest14.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Roza Aceska; McKailyn Lort; Allison Ripperger (2026). *Ornaments and Difference Distance Magic Oriented Graphs*. DOI: [10.48550/arXiv.2606.16001](https://doi.org/10.48550/arXiv.2606.16001). URL: <https://arxiv.org/abs/2606.16001v3>.

*Commentary.*

On Fin 14, label vertex i by its integer value plus one. The 23 arcs are (0,4), (0,11), (1,4), (1,10), (2,8), (3,2), (3,12), (4,2), (5,3), (5,9), (6,1), (6,11), (7,0), (7,10), (8,0), (8,1), (9,3), (9,12), (10,9), (11,7), (12,13), (13,5), (13,6). Incoming and outgoing label sums agree at every vertex. A spanning tree connects all fourteen vertices. There are no loops or opposite arcs, and the label interval is exactly 1 through 14. Thus a connected DDMOG has 23 edges, contradicting the asserted lower bound. This gives no lower bound excluding 21 or 22 edges and no general minimum formula.

## References

- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/AceskaLortRippergerSparsest14.IsConsecutiveLabeling`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/AceskaLortRippergerSparsest14.IsDDMLabeling`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/AceskaLortRippergerSparsest14.claim`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/AceskaLortRippergerSparsest14.edgeCount`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/AceskaLortRippergerSparsest14.result`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/AceskaLortRippergerSparsest14.weight`
