# Actual support coordinates of Petz recovery

## Abstract

Actual support coordinates of Petz recovery.

**Theorem 1.1 (Inverse-square-root modular coordinates).**

Lean statement: `D5/S3/Quantum/Recovery/PetzSpectralCoordinates.spectral_petz_coordinate_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzSpectralCoordinates.spectral_petz_coordinate_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alex Meiburg (2026). *Uniform power-slope control for singular relative-entropy limits*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean>.

*Commentary.*

The positive-support relative modular coordinate matrix at B^(-1/2) eta is exactly Q^(-1/2) sqrt(T), using the spectral pseudoinverse on the kernel. The proof handles repeated eigenvalues and actual finite CFC coordinates.

**Theorem 1.2 (Reconstruct the input support columns).**

Lean statement: `D5/S3/Quantum/Recovery/PetzSpectralCoordinates.petz_input_support_columns`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzSpectralCoordinates.petz_input_support_columns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alex Meiburg (2026). *Uniform power-slope control for singular relative-entropy limits*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean>.

*Commentary.*

The positive input eigenbasis coordinate identities imply sqrt(S) Psi(Y) P_R = sqrt(R). The actual input kernel containment supplies the zero-eigenvalue coordinates. This supported identity is consumed by Schwarz trace rigidity; it is not promoted to an unsupported full-space equality.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/PetzSpectralCoordinates.petz_input_support_columns`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzSpectralCoordinates.spectral_petz_coordinate_matrix`
- Dependency: [D5/S3/Quantum/Divergence/CanonicalChannelDPI](../Divergence/CanonicalChannelDPI.md)
- Dependency: [D5/S3/Quantum/Recovery/ReferencePetzChannel](ReferencePetzChannel.md)
