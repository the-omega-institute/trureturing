# The outer general position vertex-removal bound is false

## Abstract

Induced vertex deletion can raise the outer general position number by more than the deleted degree.

**Definition 1.1 (Actual induced vertex deletion).**

$$\forall V \in \mathrm{Type},\; \forall Q \in \operatorname{SimpleGraph}\left(V\right),\; \forall x \in V,\; \operatorname{vertexDelete}\left(Q, x\right) = \operatorname{induce}\left(Q, \operatorname{compl}\left(\operatorname{singleton}\left(x\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/TianDokyeesunKlavzarOuterGeneralPositionRefutation.vertexDelete` (`✓ std3`).

*Citation.* Jing Tian; Pakanun Dokyeesun; Sandi Klavzar (2025). *On the variety of general position problems under vertex and edge removal*. DOI: [10.48550/arXiv.2510.01294](https://doi.org/10.48550/arXiv.2510.01294). URL: <https://arxiv.org/html/2510.01294v2>.

*Commentary.*

The vertex carrier consists of precisely the vertices other than x. Adjacency is inherited from Q, so this is the actual graph Q-x.

**Definition 1.2 (Non-cut by component count).**

$$\forall V \in \mathrm{Type},\; \forall Q \in \operatorname{SimpleGraph}\left(V\right),\; \forall x \in V,\; (\operatorname{NonCut}\left(Q, x\right)) \Leftrightarrow (\operatorname{Nat.card}\left(\operatorname{ConnectedComponent}\left(\operatorname{vertexDelete}\left(Q, x\right)\right)\right) \le \operatorname{Nat.card}\left(\operatorname{ConnectedComponent}\left(Q\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/TianDokyeesunKlavzarOuterGeneralPositionRefutation.NonCut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A vertex is non-cut when its deletion does not increase the number of connected components. The empty graph has zero components. Hence the sole vertex of K1 is non-cut under this convention.

**Definition 1.3 (All shortest paths avoid selected internal vertices).**

$$\forall V \in \mathrm{Type},\; \forall Q \in \operatorname{SimpleGraph}\left(V\right),\; \forall S \in \operatorname{Finset}\left(V\right),\; (\operatorname{OuterPosition}\left(Q, S\right)) \Leftrightarrow (\forall u \in V,\; (u \in S) \Rightarrow (\forall v \in V,\; \forall p \in \operatorname{Walk}\left(Q, u, v\right),\; ((\operatorname{IsPath}\left(p\right)) \land (\operatorname{length}\left(p\right) = \operatorname{dist}\left(Q, u, v\right))) \Rightarrow (\forall w \in V,\; ((w \in S) \land ((w \ne u) \land (w \ne v))) \Rightarrow (\neg w \in \operatorname{support}\left(p\right)))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/TianDokyeesunKlavzarOuterGeneralPositionRefutation.OuterPosition` (`✓ std3`).

*Citation.* Jing Tian; Pakanun Dokyeesun; Sandi Klavzar (2025). *On the variety of general position problems under vertex and edge removal*. DOI: [10.48550/arXiv.2510.01294](https://doi.org/10.48550/arXiv.2510.01294). URL: <https://arxiv.org/html/2510.01294v2>.

*Commentary.*

For a selected first endpoint and any other endpoint, every shortest path excludes each selected vertex distinct from both endpoints. A shortest path is a native graph walk satisfying IsPath and having length equal to the distance. Reversal accounts for either endpoint being selected. This includes pairs within S and pairs from S to its complement, as in the source definition.

**Definition 1.4 (Maximum outer general position cardinality).**

$$\forall V \in \mathrm{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall Q \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{outerNumber}\left(Q\right) = \operatorname{sup}\left(\operatorname{filter}\left(\operatorname{OuterPosition}\left(Q\right), \operatorname{univ}\left(\operatorname{Finset}\left(V\right)\right)\right), \operatorname{Finset.card}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/TianDokyeesunKlavzarOuterGeneralPositionRefutation.outerNumber` (`✓ std3`).

*Citation.* Jing Tian; Pakanun Dokyeesun; Sandi Klavzar (2025). *On the variety of general position problems under vertex and edge removal*. DOI: [10.48550/arXiv.2510.01294](https://doi.org/10.48550/arXiv.2510.01294). URL: <https://arxiv.org/html/2510.01294v2>.

*Commentary.*

The finite supremum ranges over every finite subset of the vertex carrier satisfying OuterPosition. It is the largest such cardinality; the empty set is included. The empty graph therefore has outer number zero, and K1 has outer number one.

**Definition 1.5 (The full finite Conjecture 3.4).**

$$(claim) \Leftrightarrow (\forall V \in \mathrm{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall Q \in \operatorname{SimpleGraph}\left(V\right),\; (\operatorname{Connected}\left(Q\right)) \Rightarrow (\forall x \in V,\; (\operatorname{NonCut}\left(Q, x\right)) \Rightarrow (\operatorname{outerNumber}\left(\operatorname{vertexDelete}\left(Q, x\right)\right) \le \operatorname{outerNumber}\left(Q\right) + \operatorname{degree}\left(Q, x\right))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/TianDokyeesunKlavzarOuterGeneralPositionRefutation.claim` (`✓ std3`).

*Citation.* Jing Tian; Pakanun Dokyeesun; Sandi Klavzar (2025). *On the variety of general position problems under vertex and edge removal*. DOI: [10.48550/arXiv.2510.01294](https://doi.org/10.48550/arXiv.2510.01294). URL: <https://arxiv.org/html/2510.01294v2>.

*Commentary.*

Conjecture 3.4 in section 3.2 of arXiv:2510.01294v2 states: If x is not a cut vertex of a graph G, then gp_o(G-x) <= gp_o(G) + deg_G(x). The formal statement uses Q for the source's G. For every finite vertex type, every simple connected graph Q, and every non-cut vertex x, Conjecture 3.4 proposes the displayed inequality. The degree is the native graph degree, counting the neighbors of x. No restriction to a graph family or to a particular selected set is imposed.

**Theorem 1.6 (A 19-vertex counterexample).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/TianDokyeesunKlavzarOuterGeneralPositionRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/tian-dokyeesun-klavzar-conjecture34-refutation` (refuted) by `D5/S3/Combinatorics/Graph/TianDokyeesunKlavzarOuterGeneralPositionRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"tian-dokyeesun-klavzar-conjecture34-refutation","declaration_gid":"D5/S3/Combinatorics/Graph/TianDokyeesunKlavzarOuterGeneralPositionRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Start from a twelve-cycle and replace opposite vertices by independent sets A and B of four vertices each, retaining their cycle neighbors. The resulting H has 18 vertices. Add x adjacent to one cycle neighbor of A and the corresponding cycle neighbor of B, so G has 19 vertices. Both G and the actual deletion G-x are connected, and x has degree two. The set A union B has size eight and is outer general position in G-x. A five-color assignment in G gives a shortest-path obstruction for every distinct pair of equal color. Every outer general position set is therefore injectively colored and has size at most five. Exact edge certificates construct descending walks and bound the length of every walk, establishing the native distances. A graph isomorphism transfers the eight-vertex set to the actual induced deletion. Thus the proposed inequality would imply 8 <= 5+2, a contradiction. The simplicial-vertex bound and conditional lower bound stated separately in the source are not settled by this result.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/TianDokyeesunKlavzarOuterGeneralPositionRefutation.NonCut`
- Truth anchor: `D5/S3/Combinatorics/Graph/TianDokyeesunKlavzarOuterGeneralPositionRefutation.OuterPosition`
- Truth anchor: `D5/S3/Combinatorics/Graph/TianDokyeesunKlavzarOuterGeneralPositionRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/TianDokyeesunKlavzarOuterGeneralPositionRefutation.outerNumber`
- Truth anchor: `D5/S3/Combinatorics/Graph/TianDokyeesunKlavzarOuterGeneralPositionRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/TianDokyeesunKlavzarOuterGeneralPositionRefutation.vertexDelete`
