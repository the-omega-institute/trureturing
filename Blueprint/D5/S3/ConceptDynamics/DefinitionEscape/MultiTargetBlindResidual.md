# Multi-Target Blind Residual

## Abstract

A joint target's blind residual is the union of its components' residuals.

**Theorem 1.1 (The joint blind residual is the component union).**

$$\operatorname{FamilyBlindResidual}\left(Gamma, current, targets\right) = \operatorname{iUnion}\left(index, \operatorname{blindResidual}\left(Gamma, current, \operatorname{targets}\left(index\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscape/MultiTargetBlindResidual.familyBlindResidual_eq_iUnion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The dependent joint target uses the existing blindResidual carrier and common joint kernel.

A joint target differs exactly when one component differs, yielding the indexed-union equality.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/MultiTargetBlindResidual.familyBlindResidual_eq_iUnion`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/DefinitionKernelGalois](DefinitionKernelGalois.md)
- Dependency: [D5/S3/ConceptDynamics/Refinement/MultiTargetMinimalSufficiency](../Refinement/MultiTargetMinimalSufficiency.md)
