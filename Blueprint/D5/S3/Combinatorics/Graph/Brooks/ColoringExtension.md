# Coloring extensions and degree reduction

## Abstract

Odd closed walks contain odd cycles; finite graphs admit the greedy degree bound and color-preserving vertex extensions.

**Definition 1.1 (An actual odd cycle).**

$$\forall V \in \mathrm{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{HasOddCycle}\left(G\right) \Leftrightarrow \left(\exists x \in V,\; \exists p \in \operatorname{Walk}\left(G, x, x\right),\; \operatorname{IsCycle}\left(p\right) \land \operatorname{Odd}\left(\operatorname{length}\left(p\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Brooks/ColoringExtension.HasOddCycle` (`✓ std3`).

*Citation.* Landon Rabern (2023). *Yet another proof of Brooks' theorem*. DOI: [10.1016/j.disc.2022.113261](https://doi.org/10.1016/j.disc.2022.113261). URL: <https://github.com/brianrabern/BrooksLean/tree/1d990050d881327fc79dd51e82ba4449b4e2467d>.

*Commentary.*

An odd cycle is a closed walk satisfying the native cycle predicate and having odd length. Containing such a cycle does not by itself say that all vertices or edges belong to it.

**Theorem 1.2 (The greedy maximum-degree bound).**

$$\forall V \in \mathrm{Type},\; [\operatorname{Fintype}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \operatorname{Colorable}\left(G, \operatorname{maxDegree}\left(G\right) + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Brooks/ColoringExtension.colorable_maxDegree_succ` (`✓ std3`). ∎

*Citation.* Landon Rabern (2023). *Yet another proof of Brooks' theorem*. DOI: [10.1016/j.disc.2022.113261](https://doi.org/10.1016/j.disc.2022.113261). URL: <https://github.com/brianrabern/BrooksLean/tree/1d990050d881327fc79dd51e82ba4449b4e2467d>.

*Commentary.*

Add vertices one at a time. At most the maximum degree colors are forbidden, so one of the maximum degree plus one colors remains. The vertex type may be empty. Deleting a maximal independent set lowers the maximum degree, and adding that set back costs at most one color. Prescribed-color extensions preserve colors already assigned; they allow the later path construction to keep its endpoint colors fixed.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Brooks/ColoringExtension.HasOddCycle`
- Truth anchor: `D5/S3/Combinatorics/Graph/Brooks/ColoringExtension.colorable_maxDegree_succ`
- Dependency: [D5/S3/Combinatorics/Graph/Brooks/Coloring](Coloring.md)
