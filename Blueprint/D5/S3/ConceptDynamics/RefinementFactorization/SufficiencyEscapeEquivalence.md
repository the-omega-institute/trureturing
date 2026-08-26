# Sufficiency-Escape Equivalence

## Abstract

A target has no escape exactly when it is constant on readout fibers and descends to the realized image.

**Theorem 1.1 (Four sufficient target conditions are equivalent).**

$$\begin{gathered}\forall X, C, Y: \operatorname{Type},\\{}q: X \to C, T: X \to Y,\\{}\operatorname{ListTFAE}({[\operatorname{defectRelation}(q, T) = \emptyset, \operatorname{ker}(q) \subseteq \operatorname{ker}(T), \operatorname{FactorsThrough}(T, q), \exists Tbar: \operatorname{range}(q) \to Y, T = Tbar \circ \operatorname{rangeFactorization}(q)]}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementFactorization/SufficiencyEscapeEquivalence.sufficiency_escape_equivalence_tfae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem uses the repository's canonical defectRelation and Setoid kernel. Fiber constancy is the pinned FactorsThrough predicate.

The descending map is defined only on the realized range of q. No inhabitance assumption or extension to the whole coordinate codomain is present.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementFactorization/SufficiencyEscapeEquivalence.sufficiency_escape_equivalence_tfae`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeLaws/DirectlyProvableLaws](../DefinitionEscapeLaws/DirectlyProvableLaws.md)
- Dependency: [D5/S3/ConceptDynamics/Refinement/InductiveSufficiency](../Refinement/InductiveSufficiency.md)
- Dependency: [D5/S3/ConceptDynamics/Transportability/ModelClassTransportabilityCriterion](../Transportability/ModelClassTransportabilityCriterion.md)
