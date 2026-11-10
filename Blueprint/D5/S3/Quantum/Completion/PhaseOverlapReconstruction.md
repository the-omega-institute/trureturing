# Phase overlap reconstruction

## Abstract

Three phase-shifted pairwise distances reconstruct a complex unit-sphere overlap.

**Definition 1.1 (The three-phase pairwise overlap readout).**

$$\operatorname{phaseOverlap}\left(x, y\right) = \frac{1}{3} ((2 - \operatorname{normSq}\left(x-(1 \cdot y)\right)) + \operatorname{conj}\left(omega\right)(2 - \operatorname{normSq}\left(x-(omega \cdot y)\right)) + \operatorname{conj}\left(\operatorname{pow}\left(omega, 2\right)\right)(2 - \operatorname{normSq}\left(x-(\operatorname{pow}\left(omega, 2\right) \cdot y)\right)))$$

*Formalization.* `D5/S3/Quantum/Completion/PhaseOverlapReconstruction.phaseOverlap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The readout combines three real squared distances with the conjugate third-root coefficients. It is the finite phase lift used by the reconstruction theorem.

**Theorem 1.2 (Three pairwise phase comparisons recover the inner product).**

$$(\forall H: \operatorname{Type}\left(0\right), (\forall x: H, (\forall y: H, ((\operatorname{norm}\left(x\right) = 1 \land \operatorname{norm}\left(y\right) = 1) \Rightarrow \operatorname{phaseOverlap}\left(x, y\right) = \operatorname{inner}\left(x, y\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/PhaseOverlapReconstruction.phaseOverlap_eq_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For unit vectors, norm-square expansion turns the three distance readings into the three real Fourier coefficients of the complex inner product.

The result is conditional on the stated complex normed inner-product structure and unit norms. It introduces no measurement menu or physical probability law.

**Theorem 1.3 (The reconstructed overlap obeys the unit Born bound).**

$$(\forall H: \operatorname{Type}\left(0\right), (\forall x: H, (\forall y: H, ((\operatorname{norm}\left(x\right) = 1 \land \operatorname{norm}\left(y\right) = 1) \Rightarrow \operatorname{normSq}\left(\operatorname{phaseOverlap}\left(x, y\right)\right) \le 1))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/PhaseOverlapReconstruction.phaseOverlap_normSq_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inner-product identification and Cauchy--Schwarz give the squared-modulus bound for normalized vectors. This is an overlap bound, not a complete measurement postulate.

## Interpretation and limits

The real comparison is pairwise and symmetric at the observable level. The complex orientation survives in the three phase contexts and is recovered by a discrete Fourier coefficient. If the amplitude itself were globally path-independent, this residual phase would be removable and the geometry would become flat.

The module does not provide normalization as a physical preparation, effects, probability additivity, tensor products, entanglement, state update or continuous dynamics. Those bridges remain separate obligations.

## References

- Truth anchor: `D5/S3/Quantum/Completion/PhaseOverlapReconstruction.phaseOverlap`
- Truth anchor: `D5/S3/Quantum/Completion/PhaseOverlapReconstruction.phaseOverlap_eq_inner`
- Truth anchor: `D5/S3/Quantum/Completion/PhaseOverlapReconstruction.phaseOverlap_normSq_le_one`
- Dependency: [D5/S3/QuadraticForms/ThreeWayPositiveKernel](../../QuadraticForms/ThreeWayPositiveKernel.md)
