# A connected relatively anti-Sidorenko orientation

## Abstract

A connected relatively anti-Sidorenko orientation

**Theorem 1.1 (An affirmative answer to Question 5.3).**

$$\exists n: \mathbb{N}, \exists D: \operatorname{Digraph}(\operatorname{Fin}(n)), \operatorname{Oriented}(D) \land \operatorname{Connected}(\operatorname{U}(D)) \land \operatorname{ArcCount}(D) \operatorname{mod} 4 = 3 \land (\forall V: \operatorname{Type}, [\operatorname{Finite}(V)] \forall G: \operatorname{Digraph}(V), \operatorname{Oriented}(G) \implies \operatorname{Hom}(D, G) \leq (\frac{1}{2})^{\operatorname{EdgeCount}(\operatorname{U}(D))} \cdot \operatorname{Hom}(\operatorname{U}(D), \operatorname{U}(G)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/RelativeAntiSidorenkoArcCount.question_5_3` (`✓ std3`). ∎

*Resolves.* `Problems/bitonti-hogan-noel-tsarev-2026-question-5-3` (proved) by `D5/S3/Combinatorics/ExtremalDensity/RelativeAntiSidorenkoArcCount.question_5_3`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bitonti-hogan-noel-tsarev-2026-question-5-3","declaration_gid":"D5/S3/Combinatorics/ExtremalDensity/RelativeAntiSidorenkoArcCount.question_5_3","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Veronica Bitonti, Emma Hogan, Jonathan A. Noel and Dmitry Tsarev (2026). *Sidorenko Inequalities in Oriented Graphs*. DOI: [10.48550/arXiv.2611.23222](https://doi.org/10.48550/arXiv.2611.23222). URL: <https://arxiv.org/abs/2611.23222v1>.

*Commentary.*

Write U(D) for the simple graph obtained by forgetting arc directions. Oriented means the arc relation is asymmetric, which forbids loops and opposing arcs. ArcCount counts ordered adjacent pairs. EdgeCount counts the edges of the underlying simple graph. The two Hom counts are natural cardinalities of all adjacency-preserving vertex maps, including noninjective maps, and are coerced to rationals for the inequality. The Fin labels represent arbitrary finite pattern order. The host carrier V is any finite type, including the empty type, and the host can be disconnected.

The witness has thirteen vertices and nineteen arcs. Two copies of the four-sign K(2,4) gadget share root 0, and their other terminals are joined by the arc 1→2. Two new leaves form 11→0→12. For each fixed root image, conditioning on the two free terminal images gives exact products of signed neighbor counts for directed maps and of common-neighbor counts for undirected maps. The same branch profile occurs on both sides of the terminal arc, so interchanging the free images averages its two directions while the root remains fixed. Integer AM–GM gives a factor of 256 for each sign gadget, and the two leaves give a factor of four. The product of these three factors and the factor of two for the terminal arc is 2^19.

Bitonti, Hogan, Noel and Tsarev pose Question 5.3 using Definition 1.2. Nie and Wei give the four-sign gadget and use reversal averaging for an arc between the terminals of one copy. The construction here uses their gadget twice and holds the shared root fixed throughout the averaging.

## References

- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/RelativeAntiSidorenkoArcCount.question_5_3`
- Dependency: [D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit](ThreeClassHomomorphismLimit.md)
