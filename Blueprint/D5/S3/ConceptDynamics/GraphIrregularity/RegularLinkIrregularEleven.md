# A Regular Link-Irregular Graph on Eleven Vertices

## Abstract

A kernel-checked proof that a known six-regular graph on eleven vertices is link-irregular.

Priority. The order-eleven fact is not new here. Jannis Harder reported a six-regular link-irregular graph of order eleven on 14 December 2025, in the discussion thread attached to David Eppstein's post "Regular link-irregular graphs", and on 15 December 2025 reported an exhaustive search over all six-regular graphs on eleven vertices yielding four minimal counterexamples, noting that one of them is separated by link degree sequences except for a single pair distinguished by whether its two degree-two vertices are adjacent. The witness used here has that structure and was reported isomorphic to the published one. What this module adds is a kernel-checked proof and a general invariance lemma, not the graph and not the refutation.

Bastien and Khormali, "On the Regularity, Planarity and Edge Bounds of Link-irregular Graphs", define: "A graph G is a link-irregular graph if every two distinct vertices of G have non-isomorphic links. The link of a vertex v in G is the subgraph induced by the neighbors of v in G." Thus degrees inside a link are measured within that induced graph, not in the ambient graph.

Section 3 of the arXiv PREPRINT, arXiv:2503.21916v2, prints: "Conjecture 17. There exists a regular link-irregular graph on n vertices if and only if n >= 12." The peer-reviewed version, Discussiones Mathematicae Graph Theory 46(2) (2026) 555-568, DOI 10.7151/dmgt.2619, DOES NOT CONTAIN Conjecture 17; it was removed in revision. The refuted statement is the one printed in the arXiv preprint, not a conjecture published in DMGT.

Only the only-if direction is refuted. The if-direction, asserting existence for every n >= 12, is untouched. Relative to the published results, the contribution is that the smallest known order of a regular link-irregular graph drops from 12 to 11. The paper's Theorem 10 rules out n <= 9; n = 10 remains open. No minimality of 11, classification, or count of such graphs is claimed. The witness graph and invariant are repository constructions; the paper supplies the conjecture, definitions, and n <= 9 exclusion.

For a finite graph, take one round of degree refinement: each vertex contributes its degree paired with the multiset of its neighbors' degrees. Then collect these pairs in an outer multiset. Multiplicities are retained at both levels. The general isomorphism-invariance lemma applies to any finite graphs, independently of this witness.

In the displays, braces and square brackets on binders retain Lean's implicit parameters and typeclass instances. Type* allows an arbitrary universe, independently for each vertex type. SimpleGraph.Iso(H,H') denotes Lean's H ≃g H'; Finset.inter(A,B) denotes A ∩ B. These are notation expansions, with no hypotheses suppressed. Fin(n) has vertices labelled from 0 through n - 1; .val retains the multiset of a finset or projects a subtype to its ambient value.

**Definition 1.1 (One round of degree refinement).**

$$\begin{aligned}\forall \{ W: Type* \} [\operatorname{Fintype}(W)] [\operatorname{DecidableEq}(W)] (H: \operatorname{SimpleGraph}(W)) [\operatorname{DecidableRel}(H.Adj)],\\\operatorname{wlProfile}(H) =\\\operatorname{Multiset.map}(x \mapsto (\operatorname{H.degree}(x), \operatorname{Multiset.map}(y \mapsto \operatorname{H.degree}(y), (\operatorname{H.neighborFinset}(x)).val)), ((Finset.univ: \operatorname{Finset}(W))).val)\end{aligned}$$

*Formalization.* `D5/S3/ConceptDynamics/GraphIrregularity/RegularLinkIrregularEleven.wlProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For H on W, each x contributes its degree and the multiset of degrees of vertices adjacent to x. Mapping the underlying multiset of univ keeps repetitions of equal pairs; the inner map keeps repeated degrees.

**Theorem 1.2 (Isomorphisms preserve the refined profile).**

$$\begin{aligned}\forall \{ W W': Type* \}\\{}[\operatorname{Fintype}(W)] [\operatorname{DecidableEq}(W)] [\operatorname{Fintype}(W')] [\operatorname{DecidableEq}(W')]\\\{ H: \operatorname{SimpleGraph}(W) \} \{ H': \operatorname{SimpleGraph}(W') \}\\{}[\operatorname{DecidableRel}(H.Adj)] [\operatorname{DecidableRel}(H'.Adj)]\\(f: \operatorname{SimpleGraph.Iso}(H, H')),\\\operatorname{wlProfile}(H) = \operatorname{wlProfile}(H')\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphIrregularity/RegularLinkIrregularEleven.wlProfile_eq_of_iso` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The isomorphism f preserves degrees and bijects neighbor sets. Transporting the inner multiset along that neighbor bijection and the outer multiset along f proves equality. W and W' may be different types; all finiteness, equality, and adjacency instances are retained in the statement.

**Definition 1.3 (Compute a link profile in the ambient vertex type).**

$$\begin{aligned}\forall \{ V: Type* \} [\operatorname{Fintype}(V)] [\operatorname{DecidableEq}(V)] (G: \operatorname{SimpleGraph}(V)) [\operatorname{DecidableRel}(G.Adj)]\\(v: V),\\\operatorname{finsetLinkProfile}(G, v) =\\\operatorname{Multiset.map}(x \mapsto ((\operatorname{Finset.inter}(\operatorname{G.neighborFinset}(v), \operatorname{G.neighborFinset}(x))).card, \operatorname{Multiset.map}(y \mapsto (\operatorname{Finset.inter}(\operatorname{G.neighborFinset}(v), \operatorname{G.neighborFinset}(y))).card, (\operatorname{Finset.inter}(\operatorname{G.neighborFinset}(v), \operatorname{G.neighborFinset}(x))).val)), (\operatorname{G.neighborFinset}(v)).val)\end{aligned}$$

*Formalization.* `D5/S3/ConceptDynamics/GraphIrregularity/RegularLinkIrregularEleven.finsetLinkProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For x adjacent to v, its link degree is the cardinality of the intersection of the ambient neighbor finsets of v and x. The inner multiset records the corresponding link degrees of their common neighbors.

**Theorem 1.4 (Link degrees from ambient neighbor intersections).**

$$\begin{aligned}\forall \{ V: Type* \} [\operatorname{Fintype}(V)] [\operatorname{DecidableEq}(V)] (G: \operatorname{SimpleGraph}(V)) [\operatorname{DecidableRel}(G.Adj)]\\(v: V) (x: \operatorname{G.neighborSet}(v)),\\(\operatorname{G.induce}(\operatorname{G.neighborSet}(v))).degree x = (\operatorname{Finset.inter}(\operatorname{G.neighborFinset}(v), \operatorname{G.neighborFinset}(x.val))).card\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphIrregularity/RegularLinkIrregularEleven.link_degree_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The binder x belongs to G.neighborSet(v), not to an unrestricted ambient vertex type. The induced neighbor finset maps bijectively onto the displayed ambient intersection.

**Theorem 1.5 (The ambient computation is the induced-link invariant).**

$$\begin{aligned}\forall \{ V: Type* \} [\operatorname{Fintype}(V)] [\operatorname{DecidableEq}(V)] (G: \operatorname{SimpleGraph}(V)) [\operatorname{DecidableRel}(G.Adj)]\\(v: V),\\\operatorname{wlProfile}(\operatorname{G.induce}(\operatorname{G.neighborSet}(v))) = \operatorname{finsetLinkProfile}(G, v)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphIrregularity/RegularLinkIrregularEleven.wlProfile_induce_eq_finsetLinkProfile` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equality includes both multiset levels. It transfers the general isomorphism invariant to an ambient computation without erasing multiplicities or changing the induced graph.

For this witness, the measured plain degree multisets distinguish only 10 of the 11 links. The links at vertices 1 and 5 share the degree multiset {2,2,3,3,3,3}. One round of refinement separates all 11 links. This collision is a measured fact about this witness, not a general theorem about regular graphs or graph invariants.

**Definition 1.6 (The explicit eleven-vertex witness).**

$$witnessGraph: \operatorname{SimpleGraph}(\operatorname{Fin}(11)) = \operatorname{SimpleGraph.fromRel}(u v \mapsto (u, v) \in witnessEdges)$$

*Formalization.* `D5/S3/ConceptDynamics/GraphIrregularity/RegularLinkIrregularEleven.witnessGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The repository witness has 11 vertices, 33 undirected edges, and degree 6 at every vertex. SimpleGraph.fromRel symmetrizes the listed relation and excludes loops. Each edge below is listed once, smaller endpoint first.

witnessEdges = [(0,2), (0,4), (0,5), (0,8), (0,9), (0,10), (1,2), (1,3), (1,5), (1,7), (1,8), (1,10), (2,4), (2,5), (2,9), (2,10), (3,6), (3,7), (3,8), (3,9), (3,10), (4,5), (4,6), (4,7), (4,9), (5,6), (5,8), (6,8), (6,9), (6,10), (7,8), (7,9), (7,10)].

**Definition 1.7 (The witness's link profiles).**

$$\forall (v: \operatorname{Fin}(11)), \operatorname{linkProfile}(v) = \operatorname{finsetLinkProfile}(witnessGraph, v)$$

*Formalization.* `D5/S3/ConceptDynamics/GraphIrregularity/RegularLinkIrregularEleven.linkProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each profile is a multiset of pairs of a natural number and a multiset of natural numbers, obtained by specializing finsetLinkProfile.

**Theorem 1.8 (Every witness vertex has degree six).**

$$\operatorname{witnessGraph.IsRegularOfDegree}(6)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphIrregularity/RegularLinkIrregularEleven.witness_regular` (`✓ std3`). ∎

*Citation.* Jannis Harder (2025). *Computational search for regular link-irregular graphs, Mathstodon thread of 14 and 15 December 2025*. URL: <https://mathstodon.xyz/@11011110/115716795916671285>.

*Commentary.*

Lean proves six-regularity by finite decision.

**Theorem 1.9 (All eleven refined link profiles are distinct).**

$$\forall u v: \operatorname{Fin}(11), u \neq v \Rightarrow \operatorname{linkProfile}(u) \neq \operatorname{linkProfile}(v)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphIrregularity/RegularLinkIrregularEleven.witness_profiles_pairwise_ne` (`✓ std3`). ∎

*Citation.* Jannis Harder (2025). *Computational search for regular link-irregular graphs, Mathstodon thread of 14 and 15 December 2025*. URL: <https://mathstodon.xyz/@11011110/115716795916671285>.

*Commentary.*

The distinctness hypothesis u ≠ v is essential. Lean certifies the universally quantified implication using decide +kernel.

**Definition 1.10 (Pairwise non-isomorphic links).**

$$\begin{aligned}\forall \{ V: Type* \} [\operatorname{Fintype}(V)] [\operatorname{DecidableEq}(V)] (G: \operatorname{SimpleGraph}(V)) [\operatorname{DecidableRel}(G.Adj)],\\\operatorname{LinkIrregular}(G) \iff\\\forall u v: V, u \neq v \Rightarrow\\\operatorname{IsEmpty}(\operatorname{SimpleGraph.Iso}(\operatorname{G.induce}(\operatorname{G.neighborSet}(u)), \operatorname{G.induce}(\operatorname{G.neighborSet}(v))))\end{aligned}$$

*Formalization.* `D5/S3/ConceptDynamics/GraphIrregularity/RegularLinkIrregularEleven.LinkIrregular` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

IsEmpty asserts that the type of graph isomorphisms between the two induced neighborhoods has no inhabitants. This implements the paper's definition for finite simple graphs.

**Definition 1.11 (The preprint's only-if direction).**

$$\begin{aligned}regularLinkIrregularOnlyFromTwelve \iff\\\forall (n: Nat) (G: \operatorname{SimpleGraph}(\operatorname{Fin}(n))) (r: Nat),\\2 \leq n \Rightarrow \operatorname{G.IsRegularOfDegree}(r) \Rightarrow \operatorname{LinkIrregular}(G) \Rightarrow 12 \leq n\end{aligned}$$

*Formalization.* `D5/S3/ConceptDynamics/GraphIrregularity/RegularLinkIrregularEleven.regularLinkIrregularOnlyFromTwelve` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The quantifiers cover every order n with at least two vertices, every simple graph on Fin(n), and every natural degree r. Both regularity and link-irregularity are hypotheses. Lean supplies the decidability instances classically inside this closed proposition; the if-direction is not encoded.

**Theorem 1.12 (The witness has pairwise non-isomorphic links).**

$$\operatorname{LinkIrregular}(witnessGraph)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphIrregularity/RegularLinkIrregularEleven.witness_link_irregular` (`✓ std3`). ∎

*Citation.* Jannis Harder (2025). *Computational search for regular link-irregular graphs, Mathstodon thread of 14 and 15 December 2025*. URL: <https://mathstodon.xyz/@11011110/115716795916671285>.

*Commentary.*

An isomorphism of two distinct links would equate their wlProfiles. The induced-link equality would then equate their linkProfiles, contradicting witness_profiles_pairwise_ne.

**Theorem 1.13 (The preprint's asserted lower bound is false).**

$$\neg regularLinkIrregularOnlyFromTwelve$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphIrregularity/RegularLinkIrregularEleven.not_regularLinkIrregularOnlyFromTwelve` (`✓ std3`). ∎

*Citation.* Jannis Harder (2025). *Computational search for regular link-irregular graphs, Mathstodon thread of 14 and 15 December 2025*. URL: <https://mathstodon.xyz/@11011110/115716795916671285>.

*Commentary.*

This closed theorem has no hypotheses. Apply the claimed bound to n = 11, G = witnessGraph, and r = 6. The two witness theorems would imply 12 ≤ 11, a contradiction. This refutes only the only-if direction printed in arXiv:2503.21916v2. It neither establishes nor refutes existence for every n >= 12. Order 10 remains open; 11 is not claimed minimal. No classification or count of regular link-irregular graphs is claimed.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GraphIrregularity/RegularLinkIrregularEleven.LinkIrregular`
- Truth anchor: `D5/S3/ConceptDynamics/GraphIrregularity/RegularLinkIrregularEleven.finsetLinkProfile`
- Truth anchor: `D5/S3/ConceptDynamics/GraphIrregularity/RegularLinkIrregularEleven.linkProfile`
- Truth anchor: `D5/S3/ConceptDynamics/GraphIrregularity/RegularLinkIrregularEleven.link_degree_eq`
- Truth anchor: `D5/S3/ConceptDynamics/GraphIrregularity/RegularLinkIrregularEleven.not_regularLinkIrregularOnlyFromTwelve`
- Truth anchor: `D5/S3/ConceptDynamics/GraphIrregularity/RegularLinkIrregularEleven.regularLinkIrregularOnlyFromTwelve`
- Truth anchor: `D5/S3/ConceptDynamics/GraphIrregularity/RegularLinkIrregularEleven.witnessGraph`
- Truth anchor: `D5/S3/ConceptDynamics/GraphIrregularity/RegularLinkIrregularEleven.witness_link_irregular`
- Truth anchor: `D5/S3/ConceptDynamics/GraphIrregularity/RegularLinkIrregularEleven.witness_profiles_pairwise_ne`
- Truth anchor: `D5/S3/ConceptDynamics/GraphIrregularity/RegularLinkIrregularEleven.witness_regular`
- Truth anchor: `D5/S3/ConceptDynamics/GraphIrregularity/RegularLinkIrregularEleven.wlProfile`
- Truth anchor: `D5/S3/ConceptDynamics/GraphIrregularity/RegularLinkIrregularEleven.wlProfile_eq_of_iso`
- Truth anchor: `D5/S3/ConceptDynamics/GraphIrregularity/RegularLinkIrregularEleven.wlProfile_induce_eq_finsetLinkProfile`
