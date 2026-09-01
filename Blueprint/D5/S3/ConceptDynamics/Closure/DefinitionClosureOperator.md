# Definition Closure as an Upstream Closure Operator

## Abstract

The repository semantic definition closure is bundled as Mathlib's canonical closure operator.

**Theorem 1.1 (Upstream closed families are exactly semantically closed families).**

$$\forall Gamma, \operatorname{IsClosed}(\operatorname{definitionClosureOperator}(), Gamma) \iff \operatorname{DefinitionClosure}(Gamma) = Gamma.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Closure/DefinitionClosureOperator.isClosed_definitionClosureOperator_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The repository already proves that DefinitionClosure is extensive, monotone, and literally idempotent on same-codomain readout families.

Those laws are bundled as Mathlib's ClosureOperator without introducing a second closure operation. Its closed-element carrier is therefore available to standard order-theoretic APIs.

A family is closed exactly when it contains every readout constant on the family's common observational kernel.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Closure/DefinitionClosureOperator.isClosed_definitionClosureOperator_iff`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/DefinitionKernelGalois](../DefinitionEscape/DefinitionKernelGalois.md)
