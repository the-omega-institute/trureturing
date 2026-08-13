# Church-Rosser Equivalence

## Abstract

Global confluence is equivalent to the Church-Rosser convertibility-iff-joinability characterization.

**Theorem 1.1 (Confluence iff convertibility is joinability).**

$$(\forall h, a, b, \operatorname{ReflTransGen}(r)(h, a) \land \operatorname{ReflTransGen}(r)(h, b) \Rightarrow \exists c, \operatorname{ReflTransGen}(r)(a, c) \land \operatorname{ReflTransGen}(r)(b, c).\iff (\forall a, b, \operatorname{EqvGen}(r)(a, b) \iff \operatorname{Join} \operatorname{ReflTransGen}(r)(a, b)).$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/ChurchRosser.confluent_iff_church_rosser` (`✓ std3`). ∎

*Citation.* Alonzo Church and J. B. Rosser (1936). *Some Properties of Conversion*. DOI: [10.1090/S0002-9947-1936-1501858-0](https://doi.org/10.1090/S0002-9947-1936-1501858-0).

*Commentary.*

The forward direction makes joinability an equivalence via Relation.equivalence_join, then eliminates EqvGen by its closure constructors.

The reverse direction turns two reductions from one source into a convertibility path through that source. No termination hypothesis is needed.

The Newman corollary composes this equivalence with the frozen D5/S0/Rewriting/NewmanConfluence.newman_confluent theorem; Mathlib's Relation.church_rosser remains a stronger sufficient criterion.

**Theorem 1.2 (Newman to Church-Rosser).**

$$\operatorname{WellFounded}(\operatorname{swap}(r)) \land \text{locally confluent} \Rightarrow (\forall a, b, \operatorname{EqvGen}(r)(a, b) \iff \operatorname{Join} \operatorname{ReflTransGen}(r)(a, b).$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/ChurchRosser.newman_church_rosser` (`✓ std3`). ∎

*Citation.* M. H. A. Newman (1942). *On Theories with a Combinatorial Definition of "Equivalence"*. DOI: [10.2307/1968867](https://doi.org/10.2307/1968867).

*Commentary.*

This theorem is a one-composition corollary of the generic equivalence and the frozen Newman confluence theorem.

## References

- Truth anchor: `D5/S0/Rewriting/ChurchRosser.confluent_iff_church_rosser`
- Truth anchor: `D5/S0/Rewriting/ChurchRosser.newman_church_rosser`
- Dependency: [D5/S0/Rewriting/NewmanConfluence](NewmanConfluence.md)
