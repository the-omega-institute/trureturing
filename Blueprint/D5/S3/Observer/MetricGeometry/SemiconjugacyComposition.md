# Semiconjugacy Defect Under Composition

## Abstract

A Lipschitz post-map bounds composite defect by its two component defects.

**Theorem 1.1 (Semiconjugacy defect is subadditive under composition).**

$$\delta(\rho\circ\pi; \tau, \omega) \leq K \delta(\pi; \tau, \sigma) + \delta(\rho; \sigma, \omega).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/SemiconjugacyComposition.semiconjugacy_defect_composition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Define each defect as the supremum of the extended distance between projecting after the source update and applying the target update after projection. For a K-Lipschitz post-map, insert the intermediate updated projection. The triangle inequality splits the resulting distance, the Lipschitz estimate bounds the first term, and each pointwise term is bounded by its defining supremum.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometry/SemiconjugacyComposition.semiconjugacy_defect_composition`
