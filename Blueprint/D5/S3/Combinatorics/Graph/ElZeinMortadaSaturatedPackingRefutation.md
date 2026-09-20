# A Seven-Vertex Saturated Packing Refutation

## Abstract

A connected seven-vertex graph refutes the printed saturated-subcubic packing conjecture.

**Definition 1.1 (Subcubic graphs).**

$$\forall V \in \mathrm{Type},\; (\operatorname{Fintype}\left(V\right)) \Rightarrow (\forall G \in \operatorname{SimpleGraph}\left(V\right),\; (\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)) \Rightarrow ((\operatorname{Subcubic}\left(G\right)) \Leftrightarrow (\forall v \in V,\; \operatorname{degree}\left(G, v\right) \le 3)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/ElZeinMortadaSaturatedPackingRefutation.Subcubic` (`✓ std3`).

*Citation.* Ayman El Zein, Maidoun Mortada (2026). *Impact of local girth on the S-packing coloring of k-saturated subcubic graphs*. DOI: [10.48550/arXiv.2603.25113](https://doi.org/10.48550/arXiv.2603.25113). URL: <https://arxiv.org/abs/2603.25113v1>.

*Commentary.*

A finite simple graph is subcubic exactly when every vertex has degree at most three.

**Definition 1.2 (Saturated subcubic graphs).**

$$\forall V \in \mathrm{Type},\; ((\operatorname{Fintype}\left(V\right)) \land (\operatorname{DecidableEq}\left(V\right))) \Rightarrow (\forall k \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; (\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)) \Rightarrow ((\operatorname{Saturated}\left(k, G\right)) \Leftrightarrow (\forall v \in V,\; (\operatorname{degree}\left(G, v\right) = 3) \Rightarrow (\operatorname{card}\left(\{u: V \in \operatorname{neighborFinset}\left(G, v\right) \mid \operatorname{degree}\left(G, u\right) = 3\}\right) \le k))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/ElZeinMortadaSaturatedPackingRefutation.Saturated` (`✓ std3`).

*Citation.* Ayman El Zein, Maidoun Mortada (2026). *Impact of local girth on the S-packing coloring of k-saturated subcubic graphs*. DOI: [10.48550/arXiv.2603.25113](https://doi.org/10.48550/arXiv.2603.25113). URL: <https://arxiv.org/abs/2603.25113v1>.

*Commentary.*

For a natural number k, saturation requires each degree-three vertex to have at most k neighbours that also have degree three. The displayed filtered neighbour set is the defining expression.

**Definition 1.3 (The (1,1,2)-packing condition).**

$$\forall V \in \mathrm{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; (\operatorname{IsPacking112}\left(G\right)) \Leftrightarrow (\exists c \in (V) \to (\operatorname{Fin}\left(3\right)),\; \forall u \in V,\; \forall v \in V,\; (u \ne v) \Rightarrow ((\operatorname{c}\left(u\right) = \operatorname{c}\left(v\right)) \Rightarrow (\operatorname{if}\left(\operatorname{c}\left(u\right) = 2, 2: \mathrm{ENat} < \operatorname{edist}\left(G, u, v\right), 1: \mathrm{ENat} < \operatorname{edist}\left(G, u, v\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/ElZeinMortadaSaturatedPackingRefutation.IsPacking112` (`✓ std3`).

*Citation.* Ayman El Zein, Maidoun Mortada (2026). *Impact of local girth on the S-packing coloring of k-saturated subcubic graphs*. DOI: [10.48550/arXiv.2603.25113](https://doi.org/10.48550/arXiv.2603.25113). URL: <https://arxiv.org/abs/2603.25113v1>.

*Commentary.*

The fibres of c partition V into three classes, including the possibility of empty classes. Equal colors zero and one require extended distance greater than one, while color two requires extended distance greater than two. Extended distance is infinity across distinct components; ordinary SimpleGraph.dist instead returns zero when no path exists, which would not express the graph-distance convention for disconnected graphs.

**Definition 1.4 (The printed Conjecture 3).**

$$(claim) \Leftrightarrow (\forall V \in \mathrm{Type},\; (\operatorname{Fintype}\left(V\right)) \Rightarrow ((\operatorname{DecidableEq}\left(V\right)) \Rightarrow (\forall G \in \operatorname{SimpleGraph}\left(V\right),\; (\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)) \Rightarrow ((\operatorname{Subcubic}\left(G\right)) \Rightarrow ((\operatorname{Saturated}\left(2, G\right)) \Rightarrow (\operatorname{IsPacking112}\left(G\right)))))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/ElZeinMortadaSaturatedPackingRefutation.claim` (`✓ std3`).

*Citation.* Ayman El Zein, Maidoun Mortada (2026). *Impact of local girth on the S-packing coloring of k-saturated subcubic graphs*. DOI: [10.48550/arXiv.2603.25113](https://doi.org/10.48550/arXiv.2603.25113). URL: <https://arxiv.org/abs/2603.25113v1>.

*Commentary.*

The source definitions read verbatim: "A graph G is said to be subcubic if ∆(G) ≤ 3 […]." "A subcubic graph is said to be k-saturated, for 0 ≤ k ≤ 3, if every vertex of degree 3 is adjacent to at most k vertices of degree 3." "Given a non-decreasing sequence of positive integers S = (s₁, s₂, …, s_k), an S-packing coloring of a graph G is a partition of V(G) into subsets V₁, V₂, …, V_k such that for any two distinct vertices u, v ∈ V_i, we have dist_G(u, v) > s_i." Conjecture 3 reads verbatim: "Every 2-saturated subcubic graph is (1, 1, 2)-packing colorable." The displayed conjecture has no local-girth hypothesis. The quantified type V is in universe zero, so claim is a closed proposition.

**Theorem 1.5 (Conjecture 3 is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ElZeinMortadaSaturatedPackingRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The graph with graph6 encoding FhcYG has edges 01, 04, 12, 16, 23, 34, 35, 45, and 56. Its degree sequence is 2,3,2,3,3,3,2, and its four degree-three vertices have 0,2,2,2 degree-three neighbours. The triangle on 3,4,5 forces one triangle vertex into color two. Every vertex is at extended distance at most two from each triangle vertex, so no other vertex can have color two. Deleting 3, 4, or 5 leaves respectively the five-cycles 0-1-6-5-4-0, 1-2-3-5-6-1, or 0-1-2-3-4-0. The remaining six vertices therefore cannot be split between the two independent radius-one classes.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ElZeinMortadaSaturatedPackingRefutation.IsPacking112`
- Truth anchor: `D5/S3/Combinatorics/Graph/ElZeinMortadaSaturatedPackingRefutation.Saturated`
- Truth anchor: `D5/S3/Combinatorics/Graph/ElZeinMortadaSaturatedPackingRefutation.Subcubic`
- Truth anchor: `D5/S3/Combinatorics/Graph/ElZeinMortadaSaturatedPackingRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/ElZeinMortadaSaturatedPackingRefutation.result`
