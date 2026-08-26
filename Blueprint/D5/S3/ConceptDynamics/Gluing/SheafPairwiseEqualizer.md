# Sheaf Pairwise Equalizer

## Abstract

Global sections of a type-valued sheaf are exactly compatible local sections.

**Theorem 1.1 (The pairwise restriction equalizer classifies global sections).**

$$\forall C \in \operatorname{Type}\left(\right), U \in \operatorname{Object}\left(C\right), E \in \operatorname{PreZeroHypercover}\left(U\right), F \in \operatorname{TypePresheaf}\left(C\right),\; \left(\operatorname{Category}\left(C\right) \land \left(\operatorname{PairwisePullbacks}\left(E\right) \land \operatorname{SheafFor}\left(F, E\right)\right)\right) \Rightarrow \exists e: \operatorname{GlobalSections}\left(F, U\right) \equiv \operatorname{PairwiseOverlapEqualizer}\left(F, E\right), ((\forall s \in \operatorname{GlobalSections}\left(F, U\right),\; e\left(s\right) = \operatorname{restriction}\left(F, E\right)\left(s\right)) \land (\forall a: \operatorname{PairwiseOverlapEqualizer}\left(F, E\right), \exists! s: \operatorname{GlobalSections}\left(F, U\right), \operatorname{restriction}\left(F, E\right)\left(s\right) = a))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Gluing/SheafPairwiseEqualizer.sheaf_sections_equiv_pairwise_equalizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A pre-zero hypercover records the cover maps U_i to U. Its canonical pre-one hypercover uses U_i times over U with U_j for every pair, so its section type is the displayed pairwise equalizer.

The equivalence is required to agree pointwise with the canonical restriction map. Consequently every compatible local family is the restriction of exactly one global section.

Pinned Mathlib supplies the hypercover, pairwise-pullback equalizer, and sheaf-bijectivity lemmas used directly in the proof. Repository search found no existing D5 declaration with both public clauses.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Gluing/SheafPairwiseEqualizer.sheaf_sections_equiv_pairwise_equalizer`
