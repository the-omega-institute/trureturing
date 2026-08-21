# Relative-Entropy Defect Composition

## Abstract

Relative-entropy loss telescopes exactly along two composable state channels.

**Theorem 1.1 (Relative-entropy defects form an additive channel chain).**

$$\delta_{\psi\circ\phi}(\rho, \sigma) = \delta_{\phi}(\rho, \sigma) + \delta_{\psi}(\phi\rho, \phi\sigma).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/RelativeEntropyDefectComposition.relative_entropy_defect_composition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each state channel, its defect is the source relative entropy minus the target relative entropy after applying the channel.

Expanding the three defects makes the intermediate relative entropy cancel, leaving the exact composition identity.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/RelativeEntropyDefectComposition.relative_entropy_defect_composition`
- Dependency: [D5/S3/Observer/DefectComposition/StrictDefectComposition](../../Observer/DefectComposition/StrictDefectComposition.md)
