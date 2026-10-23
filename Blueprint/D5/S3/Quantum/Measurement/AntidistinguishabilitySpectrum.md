# AntidistinguishabilitySpectrum

## Abstract

Finite-dimensional spectral and overlap bounds for antidistinguishability.

**Definition 1.1 (SpectralBalanced).**

$$\forall (n : \mathbb{N}) \{G : Matrix (Fin n) (Fin n) \mathbb{C}\} (hG : G . IsHermitian) , SpectralBalanced hG = \forall (j : Fin n) , Real . sqrt (hG . eigenvalues j) \leq \sum i \in univ . erase j , Real . sqrt (hG . eigenvalues i)$$

*Formalization.* `D5/S3/Quantum/Measurement/AntidistinguishabilitySpectrum.SpectralBalanced` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The displayed predicate compares every eigenvalue square root against the sum over its complement. It organizes the spectral pairing proof.

**Theorem 1.2 (spectral balanced pairing nonneg).**

$$\forall (n : \mathbb{N}) , (1 \leq n) \to \forall (G Y : Matrix (Fin n) (Fin n) \mathbb{C}) (hG : G . PosSemidef) , (SpectralBalanced hG . isHermitian) \to (LocallyPsd Y) \to RHLinalg . rtrace (G \cdot Y) \geq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/AntidistinguishabilitySpectrum.spectral_balanced_pairing_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Theorem 1.3 (spectral sufficient antidistinguishable).**

$$\forall (n d : \mathbb{N}) , (2 \leq n) \to \forall (\psi : Fin n \to EuclideanSpace \mathbb{C} (Fin d)) , (Real . sqrt ((fun k : Fin n \mapsto (gramPsd \psi) . isHermitian . eigenvalues (((finCongr (n = Fintype . card (Fin n))) . trans RHLinalg . eigEquiv) k)) \langle 0\rangle) \leq \sum i \in univ . erase (\langle 0\rangle : Fin n) , Real . sqrt ((fun k : Fin n \mapsto (gramPsd \psi) . isHermitian . eigenvalues (((finCongr (n = Fintype . card (Fin n))) . trans RHLinalg . eigEquiv) k)) i)) \to IsAntidistinguishable \psi$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/AntidistinguishabilitySpectrum.spectral_sufficient_antidistinguishable` (`✓ std3`). ∎

*Citation.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

Theorem 5.1, page 12: “Let n ≥ 2 be an integer and let G ∈ Pos(ℂⁿ) be the Gram matrix of a set S of n pure states, and let λ₀ ≥ λ₁ ≥ ⋯ ≥ λₙ₋₁ be the eigenvalues of G.” Its displayed square-root inequality implies antidistinguishability. The ordered values are read through the canonical finite eigenvalue equivalence. The displayed Lean implication also applies to unnormalized vectors; normalization is not used in this implication.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/AntidistinguishabilitySpectrum.SpectralBalanced`
- Truth anchor: `D5/S3/Quantum/Measurement/AntidistinguishabilitySpectrum.spectral_balanced_pairing_nonneg`
- Truth anchor: `D5/S3/Quantum/Measurement/AntidistinguishabilitySpectrum.spectral_sufficient_antidistinguishable`
- Dependency: [D5/S3/Quantum/Measurement/IncoherentCone](IncoherentCone.md)
- Dependency: [D5/S3/Quantum/Measurement/LocallyPositiveSpectrum](LocallyPositiveSpectrum.md)
