# A Dom-Path Longer Than the Jaco Graph Diameter Bound

## Abstract

The finite linear Jaco graph on 33 vertices refutes Kok's dom-path diameter conjecture.

**Definition 1.1 (One-indexed Jaco vertices).**

$$\forall n \in \mathrm{Nat},\; \operatorname{Vertex}\left(n\right) = \{i: \mathrm{Nat} \mid (1 \le i) \land (i \le n)\}$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoDomPathDiameterRefutation.Vertex` (`✓ std3`).

*Citation.* Johan Kok (2025). *Integer sequences with conjectured relation with certain graph parameters of the family of linear Jaco graphs*. DOI: [10.48550/arXiv.2507.16500](https://doi.org/10.48550/arXiv.2507.16500).

*Commentary.*

Vertex n is the subtype of natural indices from 1 through n. This preserves the paper's labels v_1 through v_n rather than shifting them to zero.

**Definition 1.2 (The finite linear Jaco graph).**

$$\forall n \in \mathrm{Nat},\; \forall a \in \operatorname{Vertex}\left(n\right),\; \forall b \in \operatorname{Vertex}\left(n\right),\; (\operatorname{Adj}\left(\operatorname{jaco}\left(n\right), a, b\right)) \Leftrightarrow (\operatorname{Adj}\left(\operatorname{val}\left(a\right), \operatorname{val}\left(b\right)\right))$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoDomPathDiameterRefutation.jaco` (`✓ std3`).

*Citation.* Johan Kok (2025). *Integer sequences with conjectured relation with certain graph parameters of the family of linear Jaco graphs*. DOI: [10.48550/arXiv.2507.16500](https://doi.org/10.48550/arXiv.2507.16500).

*Commentary.*

The graph jaco n restricts the frozen infinite Jaco adjacency to the one-indexed vertices through n. Truncation removes only neighbors whose indices exceed n.

**Definition 1.3 (Positions occupied by a vertex set).**

$$\forall n \in \mathrm{Nat},\; \forall u \in \operatorname{Vertex}\left(n\right),\; \forall v \in \operatorname{Vertex}\left(n\right),\; \forall w \in \operatorname{Walk}\left(\operatorname{jaco}\left(n\right), u, v\right),\; \forall D \in \operatorname{Finset}\left(\operatorname{Vertex}\left(n\right)\right),\; \operatorname{positions}\left(w, D\right) = \{i: \operatorname{Fin}\left(\operatorname{length}\left(w\right) + 1\right) \mid \operatorname{getVert}\left(w, i\right) \in D\}$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoDomPathDiameterRefutation.positions` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a walk w and vertex set D, positions w D contains exactly the indices whose walk vertices lie in D. Its carrier has w.length + 1 elements.

**Definition 1.4 (Dom-paths).**

$$\forall n \in \mathrm{Nat},\; \forall h \in 1 \le n,\; \forall w \in \operatorname{Walk}\left(\operatorname{jaco}\left(n\right), (1: \operatorname{Vertex}\left(n\right)), (n: \operatorname{Vertex}\left(n\right))\right),\; (\operatorname{IsDomPath}\left(n, h, w\right)) \Leftrightarrow ((\operatorname{IsPath}\left(w\right)) \land (\exists D \in \operatorname{Finset}\left(\operatorname{Vertex}\left(n\right)\right),\; (D \subseteq \operatorname{toFinset}\left(\operatorname{support}\left(w\right)\right)) \land \left((\operatorname{IsNDominatingSet}\left(\operatorname{pathGraph}\left(\operatorname{length}\left(w\right) + 1\right), \operatorname{dominationNumber}\left(\operatorname{pathGraph}\left(\operatorname{length}\left(w\right) + 1\right)\right), \operatorname{positions}\left(w, D\right)\right)) \land (\operatorname{IsNDominatingSet}\left(\operatorname{jaco}\left(n\right), \operatorname{dominationNumber}\left(\operatorname{jaco}\left(n\right)\right), D\right))\right)))$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoDomPathDiameterRefutation.IsDomPath` (`✓ std3`).

*Citation.* Johan Kok (2025). *Integer sequences with conjectured relation with certain graph parameters of the family of linear Jaco graphs*. DOI: [10.48550/arXiv.2507.16500](https://doi.org/10.48550/arXiv.2507.16500).

*Commentary.*

Observation 2.7 (printed pages 6–7) reads verbatim: “For any finite linear Jaco graph Jn (x), n ≥ 2 there exists a pair of vertices i.e. v1 , vn for which a minimal (v1 , vn )-path (not necessarily a diam-path) i.e. Pd (Jn (x)) exists such that a γ-set of Pd (Jn (x)) is a γ-set of Jn (x). We call the path Pd (Jn (x)) the primary minimal dom-path.” A dom-path is a simple walk from v_1 to v_n with one set D of walk vertices. The positions of D form a minimum dominating set of the path graph, and the same D is a minimum dominating set of the finite Jaco graph.

**Definition 1.5 (Kok's Conjecture 2.9).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; \forall h \in 1 \le n,\; \exists w \in \operatorname{Walk}\left(\operatorname{jaco}\left(n\right), (1: \operatorname{Vertex}\left(n\right)), (n: \operatorname{Vertex}\left(n\right))\right),\; (\operatorname{IsDomPath}\left(n, h, w\right)) \land (\operatorname{length}\left(w\right) \le \operatorname{diam}\left(\operatorname{jaco}\left(n\right)\right) + 1))$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoDomPathDiameterRefutation.claim` (`✓ std3`).

*Citation.* Johan Kok (2025). *Integer sequences with conjectured relation with certain graph parameters of the family of linear Jaco graphs*. DOI: [10.48550/arXiv.2507.16500](https://doi.org/10.48550/arXiv.2507.16500).

*Commentary.*

Conjecture 2.9 (printed page 7) reads verbatim: “For any linear Jaco graph Jn (x), n ≥ 1 the length of a diam-path and a primary minimal dom-path Pd satisfy |Pd | − |diam(Jn (x))| ≤ 1.” For every positive n, the conjectured bound requires some dom-path whose edge length is at most the Mathlib diameter of jaco n plus one. This existential statement is the weakest consequence independent of how the source selects its primary minimal dom-path.

**Theorem 1.6 (Conjecture 2.9 is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/JacoDomPathDiameterRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/kok-jaco-dom-path-diameter-refutation` (refuted) by `D5/S3/ConceptDynamics/GraphColoring/JacoDomPathDiameterRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kok-jaco-dom-path-diameter-refutation","declaration_gid":"D5/S3/ConceptDynamics/GraphColoring/JacoDomPathDiameterRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok (2025). *Integer sequences with conjectured relation with certain graph parameters of the family of linear Jaco graphs*. DOI: [10.48550/arXiv.2507.16500](https://doi.org/10.48550/arXiv.2507.16500).

*Commentary.*

At n = 33 every dominating set has at least four vertices, while a path on at most nine vertices has domination number at most three. The graph diameter is at most seven, so any path allowed by the conjectured bound would have at most nine vertices, giving a contradiction. A ten-vertex dom-path exists, so the contradiction is not caused by an empty notion.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoDomPathDiameterRefutation.IsDomPath`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoDomPathDiameterRefutation.Vertex`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoDomPathDiameterRefutation.claim`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoDomPathDiameterRefutation.jaco`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoDomPathDiameterRefutation.positions`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoDomPathDiameterRefutation.result`
- Dependency: [D5/S0/Certificates/JacoExponentialDominationRefutation](../../../S0/Certificates/JacoExponentialDominationRefutation.md)
- Dependency: [D5/S3/ConceptDynamics/GraphColoring/GraphCoverDomination](GraphCoverDomination.md)
