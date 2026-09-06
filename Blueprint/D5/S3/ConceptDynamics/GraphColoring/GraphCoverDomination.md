# Regular Graph Covers and Domination

## Abstract

Every finite regular simple graph has a positive-fold cover dominated by one section.

**Definition 1.1 (Covering projection and fold).**

$$\begin{gathered}\forall V: \operatorname{Type},W: \operatorname{Type},F: \operatorname{SimpleGraph}\left(V\right),G: \operatorname{SimpleGraph}\left(W\right),p: W \to V,k: \mathbb{N},\\{}\operatorname{IsCover}\left(G, F, p, k\right)\iff(\operatorname{Surjective}\left(p\right)) \land (\forall x: W,\operatorname{BijOn}\left(p, \operatorname{neighborSet}\left(G, x\right), \operatorname{neighborSet}\left(F, \operatorname{p}\left(x\right)\right)\right)) \land (\forall v: V,\operatorname{card}\left(\{x: W \mid \operatorname{p}\left(x\right)=v\}\right)=k)\end{gathered}$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/GraphCoverDomination.IsCover` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here N_H(x) is the open neighborhood, and card is Nat.card. The map is onto, locally bijective, and has a constant fiber size. SimpleGraph supplies symmetry and excludes loops. No connectedness of G is imposed.

**Theorem 1.2 (A cover dominated by stars).**

$$\begin{gathered}\forall V: \operatorname{Type},fv: \operatorname{Fintype}\left(V\right),F: \operatorname{SimpleGraph}\left(V\right),dec: \operatorname{DecidableRel}\left(\operatorname{Adj}\left(F\right)\right),d: \mathbb{N},\operatorname{IsRegularOfDegree}\left(F, d\right) \Rightarrow \\{}\exists G: \operatorname{SimpleGraph}\left(V \times \operatorname{Option}\left(\operatorname{Fin}\left(d\right)\right)\right),(\operatorname{IsCover}\left(G, F, \operatorname{pr1}, (d+1)\right)) \land (\operatorname{dominationNumber}\left(G\right) \le \operatorname{card}\left(V\right))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/GraphCoverDomination.regular_cover_small_domination` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Walter D. Neumann (2009). *On Leighton's graph covering theorem*. DOI: [10.48550/arXiv.0906.2496](https://doi.org/10.48550/arXiv.0906.2496).

*Commentary.*

Gamma is the minimum size of a dominating set: every vertex belongs to it or has a neighbor in it. The definitions and minimum lemmas are a scoped licensed source port, identified in the Lean file. For each vertex choose a bijection between its neighbors and Fin d. The matching across an edge pairs each endpoint star with the opposite endpoint port; reverse transport is inverse transport. The stars dominate. Here pr1 denotes Prod.fst and card(V) equals Fintype.card V for a finite type. The port bijections are constructed from regularity, not assumed as an extra hypothesis. Existence of some finite cover admitting a perfect code already follows from the classical common-cover theorem; the present explicit construction is proof engineering.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/GraphCoverDomination.IsCover`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/GraphCoverDomination.regular_cover_small_domination`
