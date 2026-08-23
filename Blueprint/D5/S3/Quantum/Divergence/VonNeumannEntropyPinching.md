# Von Neumann Entropy Under Basis Pinching

## Abstract

Von Neumann entropy is compatible with quantum relative entropy, and basis pinching has an exact entropy gain when the target logarithm is diagonal.

**Lemma 1.1 (Quantum relative entropy splits into entropy and a cross term).**

$$\forall n, \rho, \sigma: \operatorname{DensityState}\left(n\right), \operatorname{quantumRelativeEntropy}\left(\rho, \sigma\right) = -\operatorname{vonNeumannEntropy}\left(\rho\right) - \operatorname{ReTr}\left(\rho \operatorname{log}\left(\sigma\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/VonNeumannEntropyPinching.quantum_relative_entropy_eq_neg_entropy_sub_cross` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two density states on the same finite-dimensional carrier, the existing quantum relative entropy is negative von Neumann entropy of the first state minus the real trace of the first state against the logarithm of the second.

This is an exact compatibility identity: expanding the relative entropy trace separates its two logarithmic terms, and the self-logarithm term is precisely the negative of the entropy definition.

**Theorem 1.2 (Basis pinching gains exactly the relative entropy).**

$$\begin{gathered}\forall d, B: \operatorname{RankOneContext}\left(d\right), \rho, \sigma: \operatorname{DensityState}\left(d\right),\\{}\operatorname{IsRecordMeasurement}\left(\operatorname{projector}\left(B\right)\right) \land \operatorname{basisMeasurement}\left(B, \rho\right) = \sigma \land \operatorname{log}\left(\sigma\right) \in \operatorname{diagonalSubspace}\left(B\right) \Rightarrow\\{}\operatorname{vonNeumannEntropy}\left(\sigma\right) = \operatorname{vonNeumannEntropy}\left(\rho\right) + \operatorname{quantumRelativeEntropy}\left(\rho, \sigma\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/VonNeumannEntropyPinching.von_neumann_entropy_pinching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let B be a complete rank-one record measurement. If applying its basis measurement to a density state rho produces sigma, and the matrix logarithm of sigma is represented in B's diagonal Hermitian subspace, then the entropy of sigma equals the entropy of rho plus their quantum relative entropy.

The basis measurement is an orthogonal projection onto the diagonal subspace, so rho and sigma have the same trace pairing against the diagonal logarithm of sigma. Substituting that equality into the relative-entropy decomposition gives the stated exact gain.

The result is conditional on diagonal membership of the target logarithm. It does not assert unconditional entropy monotonicity, a data-processing inequality, or nonnegativity of the relative entropy term.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/VonNeumannEntropyPinching.quantum_relative_entropy_eq_neg_entropy_sub_cross`
- Truth anchor: `D5/S3/Quantum/Divergence/VonNeumannEntropyPinching.von_neumann_entropy_pinching`
- Dependency: [D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition](QuantumRelativeEntropyDefectComposition.md)
- Dependency: [D5/S3/Quantum/Measurement/BasisMeasurementProjection](../Measurement/BasisMeasurementProjection.md)
