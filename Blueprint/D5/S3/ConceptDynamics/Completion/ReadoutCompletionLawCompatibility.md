# Readout and Completion Law Compatibility

## Abstract

The communication and completion modules use the same joint pushforward law.

For every finite source type, real-valued mass, readout, and target, the readout-target law is equal as a function to the completion law. The communication-side Concept type is definitionally the same function type used by the completion-side declaration.

This identification does not make an arbitrary real-valued mass a probability law: normalization and nonnegativity are not part of either constructor. It also does not identify the surrounding monotonicity and information-cost theorems, which have different inputs and conclusions.

**Theorem 1.1 (The readout-target law is the completion law).**

$$\operatorname{readoutTargetLaw}\left(\mathit{mass}, \mathit{readout}, \mathit{target}\right) = \operatorname{completionLaw}\left(\mathit{mass}, \mathit{readout}, \mathit{target}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Completion/ReadoutCompletionLawCompatibility.readoutTargetLaw_eq_completionLaw` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unfolding the two declarations and the Concept function carrier leaves the same paired pushforward on both sides.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Completion/ReadoutCompletionLawCompatibility.readoutTargetLaw_eq_completionLaw`
- Dependency: [D5/S3/ConceptDynamics/Communication/TranslationLossMonotonicity](../Communication/TranslationLossMonotonicity.md)
- Dependency: [D5/S3/ConceptDynamics/Completion/CompletionInformationCost](CompletionInformationCost.md)
