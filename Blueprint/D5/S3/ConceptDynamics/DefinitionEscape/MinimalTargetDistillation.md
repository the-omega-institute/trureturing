# Minimal Target Distillation

## Abstract

Exact target distillation removes defects without over-separation.

**Theorem 1.1 (Exact distillation is characterized by two empty residuals).**

$$\operatorname{ExactTargetDistillation}\left(current, target, added\right) \iff (\operatorname{defectRelation}\left(\operatorname{conceptJoin}\left(current, added\right), target\right) = \emptyset) \land (\operatorname{OverResidual}\left(current, target, added\right) = \emptyset).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscape/MinimalTargetDistillation.exact_distillation_iff_defect_over_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

ExactTargetDistillation compares candidate and target completion fibers; defectRelation and OverResidual remain the canonical residuals.

Exactness forces both residuals empty, while their emptiness recovers both coordinate equalities for every pair.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/MinimalTargetDistillation.exact_distillation_iff_defect_over_empty`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/QuestionAlgebraDuality](QuestionAlgebraDuality.md)
