# Boolean Markovian Response Law Characterization

## Abstract

A normalized nonnegative law on Bool x Bool is a product of two coordinate laws exactly when its two-by-two determinant vanishes.

**Theorem 1.1 (Product structure is exactly determinant vanishing).**

$$\forall P, \operatorname{isMarkovianTwoComponentLaw}(P) \iff P(tt) \cdot P(ff) = P(tf) \cdot P(ft).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/BooleanMarkovianResponseLawCharacterization.boolean_markovian_iff_determinant_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Necessity is the product determinant identity. For sufficiency, the two coordinate marginals are taken; normalization and the determinant equation show cell by cell that their product reconstructs the law.

This is the two-mode boundary case of the partial identification programme: independence of a joint Boolean response law is a single polynomial constraint on its four masses.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/BooleanMarkovianResponseLawCharacterization.boolean_markovian_iff_determinant_zero`
- Dependency: [D5/S3/ConceptDynamics/PartialIdentification/MarkovianBenefitIdentificationBoundary](MarkovianBenefitIdentificationBoundary.md)
