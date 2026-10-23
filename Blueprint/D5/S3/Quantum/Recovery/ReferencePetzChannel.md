# A reference-preserving full-space Petz channel

## Abstract

A reference-preserving full-space Petz channel.

**Definition 1.1 (Reference reset Kraus family).**

Lean statement: `D5/S3/Quantum/Recovery/ReferencePetzChannel.densityResetKraus`

*Formalization.* `D5/S3/Quantum/Recovery/ReferencePetzChannel.densityResetKraus` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alex Meiburg (2026). *Uniform power-slope control for singular relative-entropy limits*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean>.

*Commentary.*

This finite Kraus family realizes the completely positive reset X -> Tr(B X B*) S S*. It supplies the missing trace on the complement of the supported Petz core.

**Theorem 1.2 (Complete a supported Kraus map with a reference state).**

Lean statement: `D5/S3/Quantum/Recovery/ReferencePetzChannel.complete_quantum_channel_with_reference`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/ReferencePetzChannel.complete_quantum_channel_with_reference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alex Meiburg (2026). *Uniform power-slope control for singular relative-entropy limits*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean>.

*Commentary.*

A Kraus Gram sum equal to a self-adjoint projection P is completed by a reference-density reset on I-P. The conclusion is one bundled completely positive trace-preserving channel with its action proved on every input matrix. The proof uses an actual finite Kraus family, not an asserted positivity or trace law.

**Theorem 1.3 (Canonical core plus reference complement).**

Lean statement: `D5/S3/Quantum/Recovery/ReferencePetzChannel.completed_reference_petz_channel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/ReferencePetzChannel.completed_reference_petz_channel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alex Meiburg (2026). *Uniform power-slope control for singular relative-entropy limits*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean>.

*Commentary.*

For a trace-preserving Kraus channel and a reference density sigma, use the spectral inverse square root of Q=Phi(sigma), totalized as zero on ker Q. The actual supported transpose core is completed by Tr((I-P_Q) X) sigma. The result acts on every matrix and restores sigma. Singular references remain allowed. The core alone generally has trace Tr(P_Q X); the complement term is essential for a full-space channel. This channel is consumed by CanonicalPetzEquality, where it is chosen before rho. The construction is established in Hiai-Mosonyi-Petz-Beny, Quantum f-divergences and error correction, arXiv:1008.2529, full-space completion following Theorem 5.1.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/ReferencePetzChannel.complete_quantum_channel_with_reference`
- Truth anchor: `D5/S3/Quantum/Recovery/ReferencePetzChannel.completed_reference_petz_channel`
- Truth anchor: `D5/S3/Quantum/Recovery/ReferencePetzChannel.densityResetKraus`
- Dependency: [D5/S3/Quantum/Recovery/SpectralTransposeRecovery](SpectralTransposeRecovery.md)
