# Entropy Increase Under Basis Pinching

## Abstract

Basis pinching increases von Neumann entropy whenever its relative-entropy gain has an explicit nonnegativity certificate.

**Lemma 1.1 (Relative entropy is nonnegative in dimension one).**

$$\forall \rho, \sigma: \operatorname{DensityState}\left(Unit\right), 0 \leq \operatorname{quantumRelativeEntropy}\left(\rho, \sigma\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/PinchingIncreasesEntropy.quantum_relative_entropy_nonnegative_unit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A density state on the one-point carrier has a single matrix entry, and the trace-one condition forces that entry to be one. Hence both states are the unique one-dimensional density state.

Their quantum relative entropy is therefore zero, which supplies the nonnegativity certificate in dimension one. This does not prove relative-entropy nonnegativity in higher dimensions.

**Lemma 1.2 (Pinching entropy gain is relative entropy).**

$$\begin{gathered}\forall d, B: \operatorname{RankOneContext}\left(d\right), \rho, \sigma: \operatorname{DensityState}\left(d\right),\\{}d \geq 1 \land \operatorname{IsRecordMeasurement}\left(\operatorname{projector}\left(B\right)\right) \land \operatorname{basisMeasurement}\left(B, \rho\right) = \sigma \land\\{}\operatorname{log}\left(\sigma\right) \in \operatorname{diagonalSubspace}\left(B\right) \Rightarrow\\{}\operatorname{entropyGain}\left(\rho, \sigma\right) = \operatorname{quantumRelativeEntropy}\left(\rho, \sigma\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/PinchingIncreasesEntropy.pinching_entropy_gain_eq_relative_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a complete rank-one record measurement send rho to sigma, with the logarithm of sigma lying in the measurement's diagonal Hermitian subspace. The entropy gained from replacing rho by sigma is exactly their quantum relative entropy.

The preceding pinching identity expresses the entropy of sigma as the entropy of rho plus relative entropy. Subtracting the entropy of rho gives the stated gain identity.

**Theorem 1.3 (Basis pinching cannot decrease von Neumann entropy).**

$$\begin{gathered}\forall d, B: \operatorname{RankOneContext}\left(d\right), \rho, \sigma: \operatorname{DensityState}\left(d\right),\\{}d \geq 1 \land \operatorname{IsRecordMeasurement}\left(\operatorname{projector}\left(B\right)\right) \land \operatorname{basisMeasurement}\left(B, \rho\right) = \sigma \land\\{}\operatorname{log}\left(\sigma\right) \in \operatorname{diagonalSubspace}\left(B\right) \land 0 \leq \operatorname{quantumRelativeEntropy}\left(\rho, \sigma\right) \Rightarrow\\{}\operatorname{vonNeumannEntropy}\left(\rho\right) \leq \operatorname{vonNeumannEntropy}\left(\sigma\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/PinchingIncreasesEntropy.pinching_increases_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same basis-pinching and diagonal-logarithm conditions, an explicit certificate that the relative entropy of rho from sigma is nonnegative makes the entropy of sigma at least that of rho.

The exact gain identity identifies the entropy difference with the certified nonnegative relative entropy. Thus monotonicity follows without any further matrix inequality.

The certificate is an assumption in arbitrary positive dimension; this module proves it only for the one-dimensional carrier. The result does not establish the general Klein inequality, Schur--Horn pinching, or Heisenberg-side capacity monotonicity.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/PinchingIncreasesEntropy.pinching_entropy_gain_eq_relative_entropy`
- Truth anchor: `D5/S3/Quantum/Divergence/PinchingIncreasesEntropy.pinching_increases_entropy`
- Truth anchor: `D5/S3/Quantum/Divergence/PinchingIncreasesEntropy.quantum_relative_entropy_nonnegative_unit`
- Dependency: [D5/S3/Quantum/Divergence/VonNeumannEntropyPinching](VonNeumannEntropyPinching.md)
