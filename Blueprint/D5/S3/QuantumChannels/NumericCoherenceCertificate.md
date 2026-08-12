# Two-Hundred-Channel Numeric Coherence Certificate

## Abstract

Exactly two hundred phase-damping channels preserve classical zero coherence while a biased diagonal witness has Hadamard coherence seven fiftieth.

**Definition 1.1 (The biased diagonal density is the explicit state witness).**

$$rho=\operatorname{diag}(\frac{16}{25},\frac{9}{25})$$

*Formalization.* `D5/S3/QuantumChannels/NumericCoherenceCertificate.biasedDiagonalDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The witness is the non-maximally-mixed diagonal matrix diag(16/25, 9/25). Its entries are nonnegative, its trace is one, and its standard-basis off-diagonal pair is exactly zero.

**Definition 1.2 (The channel family is a finite fold over Fin 200).**

$$A(c)(\rho)=\operatorname{fold}(c,\rho)$$

*Formalization.* `D5/S3/QuantumChannels/NumericCoherenceCertificate.applyChannelFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every coefficient function c : Fin 200 -> DampingCoefficient, the definition folds exactly 200 existing phaseDamping operations over the evolving qubit matrix. The finite list is object-level and is not replaced by an iterate shorthand.

**Theorem 1.3 (The biased diagonal density is positive and normalized).**

$$\operatorname{PosSemidef}(\rho) \land \operatorname{trace}(\rho)=1$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/NumericCoherenceCertificate.biased_diagonal_density_is_state` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Entrywise positivity and exact finite trace arithmetic establish the density-state obligations for the witness.

**Theorem 1.4 (Two hundred phase-damping channels preserve zero coherence).**

$$\forall c: \operatorname{Fin}(200) \to \operatorname{Damping},\ \operatorname{offDiag}(\rho)=0 \land \operatorname{offDiag}(\operatorname{applyChannelFamily}(c,\rho))=0$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/NumericCoherenceCertificate.two_hundred_channel_zero_coherence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A one-step entrywise lemma shows that phaseDamping cannot create either off-diagonal entry from zero. List induction then proves the invariant for the complete Fin 200 fold, for every coefficient family.

**Theorem 1.5 (The Hadamard witness has exact seven-fiftieth coherence).**

$$\operatorname{offDiag}(\operatorname{hadamardCoordinates}(\rho))=(\frac{7}{50},\frac{7}{50}) \land \operatorname{offDiag}(\operatorname{hadamardCoordinates}(\rho))\neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/NumericCoherenceCertificate.biased_diagonal_hadamard_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit Hadamard coordinate formula computes both coherence entries as 7/50, which is 0.14, and norm_num proves this pair is nonzero.

**Theorem 1.6 (A concrete nonidentity two-hundred-channel family inhabits the certificate).**

$$\exists c\in \operatorname{Fin}(200),\ \operatorname{offDiag}(\operatorname{applyChannelFamily}(c,\rho))=0 \land \exists i,\ (c)\neq 1$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/NumericCoherenceCertificate.two_hundred_nonidentity_family_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking every one of the 200 coefficients to be 1/2 supplies an inhabited, genuinely nonidentity family. The same fold proof gives zero output coherence for this concrete family.

**Theorem 1.7 (The complete two-hundred-channel and Hadamard certificate).**

$$\forall c: \operatorname{Fin}(200) \to \operatorname{Damping},\ \operatorname{offDiag}(\rho)=0 \land \operatorname{offDiag}(\operatorname{applyChannelFamily}(c,\rho))=0 \land \operatorname{PosSemidef}(\rho) \land \operatorname{trace}(\rho)=1 \land \operatorname{offDiag}(\operatorname{hadamardCoordinates}(\rho))=(\frac{7}{50},\frac{7}{50})$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/NumericCoherenceCertificate.two_hundred_classical_channels_and_hadamard_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This theorem packages the exact finite certificate: all 200 object-level classical channels preserve zero standard-basis coherence, while the same physical witness has the exact nonzero Hadamard pair (7/50, 7/50).

## References

- Truth anchor: `D5/S3/QuantumChannels/NumericCoherenceCertificate.applyChannelFamily`
- Truth anchor: `D5/S3/QuantumChannels/NumericCoherenceCertificate.biasedDiagonalDensity`
- Truth anchor: `D5/S3/QuantumChannels/NumericCoherenceCertificate.biased_diagonal_density_is_state`
- Truth anchor: `D5/S3/QuantumChannels/NumericCoherenceCertificate.biased_diagonal_hadamard_certificate`
- Truth anchor: `D5/S3/QuantumChannels/NumericCoherenceCertificate.two_hundred_channel_zero_coherence`
- Truth anchor: `D5/S3/QuantumChannels/NumericCoherenceCertificate.two_hundred_classical_channels_and_hadamard_certificate`
- Truth anchor: `D5/S3/QuantumChannels/NumericCoherenceCertificate.two_hundred_nonidentity_family_witness`
- Dependency: [D5/S3/Observer/StateNotPath](../Observer/StateNotPath.md)
