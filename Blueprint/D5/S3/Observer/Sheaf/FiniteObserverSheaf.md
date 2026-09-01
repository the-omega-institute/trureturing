# Finite Observer Sheaf Cochains

## Abstract

Finite observer restrictions form a cellular zero-to-one coboundary whose kernel is the compatible-section space.

**Definition 1.1 (Finite observer network).**

Lean statement: `D5/S3/Observer/Sheaf/FiniteObserverSheaf.ObserverNetwork`

*Formalization.* `D5/S3/Observer/Sheaf/FiniteObserverSheaf.ObserverNetwork` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Vertex observations and edge overlaps are connected by linear endpoint restriction maps.

**Definition 1.2 (Observer coboundary).**

Lean statement: `D5/S3/Observer/Sheaf/FiniteObserverSheaf.observerCoboundary`

*Formalization.* `D5/S3/Observer/Sheaf/FiniteObserverSheaf.observerCoboundary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The edge defect is target restriction minus source restriction.

**Definition 1.3 (Compatible local observer family).**

Lean statement: `D5/S3/Observer/Sheaf/FiniteObserverSheaf.Compatible`

*Formalization.* `D5/S3/Observer/Sheaf/FiniteObserverSheaf.Compatible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every pair of endpoint restrictions agrees on its overlap edge.

**Definition 1.4 (Compatible-section submodule).**

Lean statement: `D5/S3/Observer/Sheaf/FiniteObserverSheaf.compatibleSections`

*Formalization.* `D5/S3/Observer/Sheaf/FiniteObserverSheaf.compatibleSections` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The global compatible families form the kernel of the observer coboundary.

**Theorem 1.5 (Compatibility is zero coboundary).**

Lean statement: `D5/S3/Observer/Sheaf/FiniteObserverSheaf.compatible_iff_coboundary_eq_zero`

*Formalization.* `D5/S3/Observer/Sheaf/FiniteObserverSheaf.compatible_iff_coboundary_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A local observer family is pairwise compatible exactly when every edge defect vanishes.

**Theorem 1.6 (Kernel membership is compatibility).**

Lean statement: `D5/S3/Observer/Sheaf/FiniteObserverSheaf.mem_compatibleSections_iff`

*Formalization.* `D5/S3/Observer/Sheaf/FiniteObserverSheaf.mem_compatibleSections_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Membership in the compatible-section submodule is equivalent to the pairwise overlap condition.

**Theorem 1.7 (Compatibility is additive).**

Lean statement: `D5/S3/Observer/Sheaf/FiniteObserverSheaf.compatible_add`

*Formalization.* `D5/S3/Observer/Sheaf/FiniteObserverSheaf.compatible_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum of two compatible local observer families remains compatible.

**Theorem 1.8 (Compatibility is stable under scaling).**

Lean statement: `D5/S3/Observer/Sheaf/FiniteObserverSheaf.compatible_smul`

*Formalization.* `D5/S3/Observer/Sheaf/FiniteObserverSheaf.compatible_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Scalar multiplication preserves compatible local observer families.

**Theorem 1.9 (Equal restrictions admit constant sections).**

Lean statement: `D5/S3/Observer/Sheaf/FiniteObserverSheaf.constant_compatible_of_same_restriction`

*Formalization.* `D5/S3/Observer/Sheaf/FiniteObserverSheaf.constant_compatible_of_same_restriction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When both endpoint restrictions coincide, every constant vertex family is compatible.

## References

- Truth anchor: `D5/S3/Observer/Sheaf/FiniteObserverSheaf.ObserverNetwork`
- Truth anchor: `D5/S3/Observer/Sheaf/FiniteObserverSheaf.observerCoboundary`
- Truth anchor: `D5/S3/Observer/Sheaf/FiniteObserverSheaf.Compatible`
- Truth anchor: `D5/S3/Observer/Sheaf/FiniteObserverSheaf.compatibleSections`
- Truth anchor: `D5/S3/Observer/Sheaf/FiniteObserverSheaf.compatible_iff_coboundary_eq_zero`
- Truth anchor: `D5/S3/Observer/Sheaf/FiniteObserverSheaf.mem_compatibleSections_iff`
- Truth anchor: `D5/S3/Observer/Sheaf/FiniteObserverSheaf.compatible_add`
- Truth anchor: `D5/S3/Observer/Sheaf/FiniteObserverSheaf.compatible_smul`
- Truth anchor: `D5/S3/Observer/Sheaf/FiniteObserverSheaf.constant_compatible_of_same_restriction`
- Dependency: [D5/S3/ConceptDynamics/Gluing/SheafPairwiseEqualizer](../../../ConceptDynamics/Gluing/SheafPairwiseEqualizer.md)
