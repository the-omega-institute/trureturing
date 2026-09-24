# Existence of Link-Irregular Tournaments

## Abstract

Link-irregular tournaments exist at every nonvacuous order exactly from six onward.

Bastien and Khormali define directed links using the union of the out- and in-neighbors and state the all-orders existence assertion as Conjecture 6. The pairwise condition is vacuous on zero and one vertices, so the exact threshold theorem is stated on the nonvacuous domain n at least two.

**Definition 1.1 (Tournament orientation).**

$$\forall V \in \operatorname{Type},\; \forall R \in V \to \left(V \to \operatorname{Prop}\right),\; (IsTournament\left(R\right)) \Leftrightarrow ((\forall v \in V,\; \neg R\left(v, v\right)) \land (\forall u \in V,\; \forall v \in V,\; (u \ne v) \Rightarrow (Xor\left(R\left(u, v\right), R\left(v, u\right)\right))))$$

*Formalization.* `D5/S3/ConceptDynamics/GraphIrregularity/LinkIrregularTournamentExistence.IsTournament` (`✓ std3`).

*Citation.* Alexander Bastien and Omid Khormali (2025). *On Link-irregular Digraphs*. URL: <https://arxiv.org/abs/2512.20494v1>.

*Commentary.*

A tournament relation is irreflexive. For every two distinct vertices, exactly one of the two possible directed edges is present. The exclusive disjunction retains both existence and uniqueness of the orientation.

**Definition 1.2 (Directed link).**

$$\forall V \in \operatorname{Type},\; \forall R \in V \to \left(V \to \operatorname{Prop}\right),\; \forall v \in V,\; DirectedLink\left(R, v\right) = Subrel\left(R, (w: V \mapsto (R\left(v, w\right)) \lor (R\left(w, v\right)))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/GraphIrregularity/LinkIrregularTournamentExistence.DirectedLink` (`✓ std3`).

*Citation.* Alexander Bastien and Omid Khormali (2025). *On Link-irregular Digraphs*. URL: <https://arxiv.org/abs/2512.20494v1>.

*Commentary.*

The carrier contains exactly the vertices w for which v points to w or w points to v. Subrel restricts the original directed relation to that carrier, so the link is the induced directed relation rather than an invariant or numerical summary.

**Definition 1.3 (Pairwise link irregularity).**

$$\forall V \in \operatorname{Type},\; \forall R \in V \to \left(V \to \operatorname{Prop}\right),\; (LinkIrregular\left(R\right)) \Leftrightarrow (\forall u \in V,\; \forall v \in V,\; (u \ne v) \Rightarrow (IsEmpty\left(RelIso\left(DirectedLink\left(R, u\right), DirectedLink\left(R, v\right)\right)\right)))$$

*Formalization.* `D5/S3/ConceptDynamics/GraphIrregularity/LinkIrregularTournamentExistence.LinkIrregular` (`✓ std3`).

*Citation.* Alexander Bastien and Omid Khormali (2025). *On Link-irregular Digraphs*. URL: <https://arxiv.org/abs/2512.20494v1>.

*Commentary.*

For each ordered pair of distinct vertices, the type of relation isomorphisms between their actual directed links is empty. RelIso is Mathlib's arbitrary bijective relation isomorphism; no selected invariant or restricted family of permutations replaces it.

**Theorem 1.4 (The exact nonvacuous threshold).**

$$\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow ((\exists R \in Fin\left(n\right) \to \left(Fin\left(n\right) \to \operatorname{Prop}\right),\; (IsTournament\left(R\right)) \land (LinkIrregular\left(R\right))) \Leftrightarrow (6 \le n))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphIrregularity/LinkIrregularTournamentExistence.result` (`✓ std3`). ∎

*Resolves.* `Problems/bastien-khormali-link-irregular-tournaments` (proved) by `D5/S3/ConceptDynamics/GraphIrregularity/LinkIrregularTournamentExistence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bastien-khormali-link-irregular-tournaments","declaration_gid":"D5/S3/ConceptDynamics/GraphIrregularity/LinkIrregularTournamentExistence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Alexander Bastien and Omid Khormali (2025). *On Link-irregular Digraphs*. URL: <https://arxiv.org/abs/2512.20494v1>.

*Acknowledgement.* James H. Schmerl and William T. Trotter (1993). *Critically indecomposable partially ordered sets, graphs, tournaments and other binary relational structures*. DOI: [10.1016/0012-365X(93)90516-V](https://doi.org/10.1016/0012-365X(93)90516-V). URL: <https://trotter.math.gatech.edu/papers/83.pdf>.

*Acknowledgement.* Houmem Belkhechine and Imed Boudabbous (2010). *Indecomposable tournaments and their indecomposable subtournaments on 5 and 7 vertices*. URL: <https://arxiv.org/abs/1007.3049v1>.

*Commentary.*

For orders two through five, every tournament has two deletion cards that are isomorphic as directed relations. The proof uses the exact one, one, two, and four isomorphism-class bounds for card orders one through four, together with pigeonhole.

At order six, the proof checks the fifteen arcs displayed in the source and excludes every relation isomorphism between every pair of cards inside the kernel. This finite calculation is confined to the proof and does not replace the quantified theorem.

For every order at least seven, take a transitive chain and an additional pivot pointing to the even zero-based chain labels and receiving arcs from the odd labels. At odd orders this is the classical W family of Schmerl--Trotter, also recalled by Belkhechine and Boudabbous; at even orders it is the preceding odd-order W with one added sink. After deleting any one chain vertex, further deletion of the pivot leaves a transitive tournament, while further deletion of any other vertex leaves an intact triangle among the pivot and one of three disjoint adjacent chain pairs. Thus the pivot is uniquely determined within each chain-deleted card, so any isomorphism between two such cards fixes it. Rigidity of the remaining finite chain then fixes every rank, and the smaller deleted rank has opposite parity on the two cards, contradicting preservation of the pivot edge. Deleting the pivot itself gives a transitive card; chain-deleted cards are not transitive.

The conclusion quantifies over all natural n satisfying 2 <= n and over all tournament relations on Fin(n). It proves both existence from six onward and nonexistence below six; orders zero and one are outside the statement because their pairwise condition is vacuous.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GraphIrregularity/LinkIrregularTournamentExistence.DirectedLink`
- Truth anchor: `D5/S3/ConceptDynamics/GraphIrregularity/LinkIrregularTournamentExistence.IsTournament`
- Truth anchor: `D5/S3/ConceptDynamics/GraphIrregularity/LinkIrregularTournamentExistence.LinkIrregular`
- Truth anchor: `D5/S3/ConceptDynamics/GraphIrregularity/LinkIrregularTournamentExistence.result`
