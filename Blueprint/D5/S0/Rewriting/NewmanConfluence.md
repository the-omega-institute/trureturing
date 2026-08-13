# Newman Confluence

## Abstract

Terminating locally confluent rewrite systems have globally joinable reductions.

**Theorem 1.1 (Every pair of reductions is joinable).**

$$\operatorname{WellFounded}(\operatorname{swap}(r)) \land (\forall h, a, b, r(h, a) \land r(h, b) \Rightarrow \exists c, \operatorname{ReflTransGen}(r)(a, c) \land \operatorname{ReflTransGen}(r)(b, c)) \Rightarrow \forall h, \forall a,b, \operatorname{ReflTransGen}(r)(h, a) \land \operatorname{ReflTransGen}(r)(h, b) \Rightarrow \exists c, \operatorname{ReflTransGen}(r)(a, c) \land \operatorname{ReflTransGen}(r)(b, c).$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/NewmanConfluence.newman_confluent` (`✓ std3`). ∎

*Citation.* M. H. A. Newman (1942). *On Theories with a Combinatorial Definition of "Equivalence"*. DOI: [10.2307/1968867](https://doi.org/10.2307/1968867).

*Commentary.*

For every terminating and locally confluent rewrite relation, any two reflexive-transitive reductions from a common source reach a common successor.

This corollary reuses the frozen unique-normal-form theorem in D5/S0/Rewriting/Newman; the pinned Mathlib version supplies Relation.ReflTransGen.trans but no matching Newman interface.

## References

- Truth anchor: `D5/S0/Rewriting/NewmanConfluence.newman_confluent`
- Dependency: [D5/S0/Rewriting/Newman](Newman.md)
