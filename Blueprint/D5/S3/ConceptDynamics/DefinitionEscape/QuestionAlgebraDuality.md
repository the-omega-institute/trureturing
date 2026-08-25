# Question Algebra Duality

## Abstract

Effective concept refinement is exactly inclusion of answerable Boolean questions.

**Theorem 1.1 (Effective refinement is equivalent to question inclusion).**

$$\operatorname{Refines}\left(\operatorname{effectiveReadout}\left(coarse\right), \operatorname{effectiveReadout}\left(fine\right)\right) \iff \operatorname{Subset}\left(\operatorname{AnswerableQuestions}\left(\operatorname{effectiveReadout}\left(coarse\right)\right), \operatorname{AnswerableQuestions}\left(\operatorname{effectiveReadout}\left(fine\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscape/QuestionAlgebraDuality.effective_refinement_iff_question_inclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Effective readouts normalize to attained-coordinate subtypes and reuse AnswerableQuestions.

Refinement transports every Boolean question; conversely, a coarse-coordinate question reconstructs the required fiber implication.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/QuestionAlgebraDuality.effective_refinement_iff_question_inclusion`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/LatentAdequacyCriterion](LatentAdequacyCriterion.md)
