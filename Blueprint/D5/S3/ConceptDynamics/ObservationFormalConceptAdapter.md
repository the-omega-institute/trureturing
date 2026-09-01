# Observation Kernels as Formal-Concept Extents

## Abstract

Readout-value incidence identifies observational equivalence classes with singleton extent closures in Mathlib formal concept analysis.

**Theorem 1.1 (A singleton extent closure is the common-kernel class).**

Lean statement: `D5/S3/ConceptDynamics/ObservationFormalConceptAdapter.extentClosure_singleton_eq_jointKernel_class`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationFormalConceptAdapter.extentClosure_singleton_eq_jointKernel_class` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An attribute is a pair consisting of one readout in the family and one output value. A state has that attribute exactly when the readout returns that value.

Closing a singleton under Mathlib's polar Galois connection therefore retains exactly the states agreeing with the original state under every readout.

The resulting set is equal to the repository joint-kernel equivalence class and hence supplies a direct adapter into the upstream complete concept lattice.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ObservationFormalConceptAdapter.extentClosure_singleton_eq_jointKernel_class`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/DefinitionKernelGalois](DefinitionEscape/DefinitionKernelGalois.md)
