# Actual support coordinates of Petz recovery

## Abstract

Actual support coordinates of Petz recovery.

**Theorem 1.1 (Hermitian spectral sum).**

$$\forall n \in \operatorname{Type},\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall H \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \forall hH \in \operatorname{Matrix.IsHermitian}\left(H\right),\; \forall f \in \mathbb{R} \to \mathbb{R},\; \operatorname{cfc}\left(f, H\right) = \sum_{(i: n)} ((\operatorname{Complex.ofReal}\left(f\left(\operatorname{Matrix.IsHermitian.eigenvalues}\left(hH, i\right)\right)\right)) \cdot (\operatorname{Matrix.vecMulVec}\left(\operatorname{fun} (x: n) \mapsto \operatorname{Matrix.IsHermitian.eigenvectorBasis}\left(hH, i, x\right), \operatorname{star}\left(\operatorname{fun} (x: n) \mapsto \operatorname{Matrix.IsHermitian.eigenvectorBasis}\left(hH, i, x\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzSpectralCoordinates.cfc_spectral_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alex Meiburg (2026). *Uniform power-slope control for singular relative-entropy limits*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean>.

*Commentary.*

For a finite Hermitian matrix, continuous functional calculus is the sum of the eigenvalue function applied to each eigenvalue times the corresponding rank-one eigenvector matrix.

**Theorem 1.2 (Inverse-square-root modular coordinates).**

Lean statement: `D5/S3/Quantum/Recovery/PetzSpectralCoordinates.spectral_petz_coordinate_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzSpectralCoordinates.spectral_petz_coordinate_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alex Meiburg (2026). *Uniform power-slope control for singular relative-entropy limits*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean>.

*Commentary.*

The positive-support relative modular coordinate matrix at B^(-1/2) eta is exactly Q^(-1/2) sqrt(T), using the spectral pseudoinverse on the kernel. The proof handles repeated eigenvalues and actual finite CFC coordinates.

**Theorem 1.3 (Reconstruct the input support columns).**

Lean statement: `D5/S3/Quantum/Recovery/PetzSpectralCoordinates.petz_input_support_columns`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzSpectralCoordinates.petz_input_support_columns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alex Meiburg (2026). *Uniform power-slope control for singular relative-entropy limits*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean>.

*Commentary.*

The positive input eigenbasis coordinate identities imply sqrt(S) Psi(Y) P_R = sqrt(R). The actual input kernel containment supplies the zero-eigenvalue coordinates. This supported identity is consumed by Schwarz trace rigidity; it is not promoted to an unsupported full-space equality.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/PetzSpectralCoordinates.cfc_spectral_sum`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzSpectralCoordinates.petz_input_support_columns`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzSpectralCoordinates.spectral_petz_coordinate_matrix`
- Dependency: [D5/S3/Quantum/Divergence/CanonicalChannelDPI](../Divergence/CanonicalChannelDPI.md)
- Dependency: [D5/S3/Quantum/Recovery/ReferencePetzChannel](ReferencePetzChannel.md)
