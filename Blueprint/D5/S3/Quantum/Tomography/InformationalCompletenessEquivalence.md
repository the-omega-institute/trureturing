# Informational Completeness Equivalence

## Abstract

Centered quantum readout completeness has four equivalent real-linear forms.

**Theorem 1.1 (Quantum informational completeness has four equivalent forms).**

$$\forall d\in \mathbb{N}, \operatorname{NeZero}\left(d\right), A: \operatorname{Type},\\{}E: A \to \operatorname{Herm}_{d}^{0},\\{}V_{0} = \operatorname{span}\left(\mathbb{R}, (E_{i}: i\in A)\right), V = \mathbb{R}I + V_{0},\\{}N = V^{\perp},\\{}\operatorname{Injective}\left((\rho: \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right) \mapsto (i: A \mapsto \Re \operatorname{Tr}\left(\operatorname{matrix}\left(\rho\right) E_{i}\right)))\right) \iff N = \{0\} \iff V = \operatorname{Herm}_{d} \iff\\{}V_{0} = \operatorname{Herm}_{d}^{0}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/InformationalCompletenessEquivalence.informational_completeness_four_way` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each E_i is a real traceless Hermitian effect direction. Its span is the centered visible space. The full visible space is constructed as the scalar identity line plus the embedded centered span, and the invisible residual is its Hilbert-Schmidt orthogonal complement.

The observer signature records the real trace expectation of every centered effect on each positive trace-one density state. Explicit perturbations about the maximally mixed state identify its injectivity with full centered span; finite-dimensional orthogonal decomposition identifies zero residual with full visibility.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/InformationalCompletenessEquivalence.informational_completeness_four_way`
- Dependency: [D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition](../Divergence/QuantumRelativeEntropyDefectComposition.md)
- Dependency: [D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition](../Entanglement/BipartiteSectorDecomposition.md)
