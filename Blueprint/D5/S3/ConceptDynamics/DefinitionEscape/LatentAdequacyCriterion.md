# Latent Adequacy Criterion

## Abstract

Target adequacy binds canonical recovery to join strictness.

**Theorem 1.1 (Joining the target is strict exactly under inadequacy).**

$$\operatorname{StrictRefinement}\left(latent, \operatorname{conceptJoin}\left(latent, target\right)\right) \iff \neg \operatorname{TargetAdequate}\left(latent, target\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscape/LatentAdequacyCriterion.latent_join_strict_iff_inadequate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

StrictRefinement and conceptJoin are the canonical carriers, while adequacy is the existing Refines recovery predicate.

Recoverability prevents strictness through the universal join factor; inadequacy supplies the missing reverse factor.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/LatentAdequacyCriterion.latent_join_strict_iff_inadequate`
- Dependency: [D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion](../Restoration/TargetRecoveryCriterion.md)
- Dependency: [D5/S3/ConceptDynamics/StrictRefinementCapability](../StrictRefinementCapability.md)
