# Definition Closure as an Upstream Closure Operator

## Abstract

The existing semantic closure of readout families is exposed through Mathlib's canonical closure-operator interface.

**Theorem 1.1 (Upstream closed families are exactly semantically closed families).**

Lean statement: `D5/S3/ConceptDynamics/Closure/DefinitionClosureOperator.isClosed_definitionClosureOperator_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Closure/DefinitionClosureOperator.isClosed_definitionClosureOperator_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The repository already proves that DefinitionClosure is extensive, monotone, and literally idempotent on same-codomain readout families.

Those laws are bundled as Mathlib ClosureOperator without introducing a second closure operation. Its closed-element carrier is therefore available to standard order-theoretic APIs.

A family is closed exactly when it contains every readout constant on the family's common observational kernel.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Closure/DefinitionClosureOperator.isClosed_definitionClosureOperator_iff`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/DefinitionKernelGalois](../DefinitionEscape/DefinitionKernelGalois.md)
