# Actual spectral whitening

## Abstract

Actual spectral smoothness used in the original reversible-channel application. The cited channel literature supplies context. The analytic proof identifies the actual CFC square root with a local inverse of the Hermitian square map; its existing six-target audit issue #18787 remains unfinished, with zero validated registrations.

**Theorem 1.1 (positive hermitian sqrt contDiffAt).**

Lean statement: `D5/S3/SpectralTopology/ActualSpectralWhitening.positive_hermitian_sqrt_contDiffAt`

*Proof.* Machine-checked in Lean as `D5/S3/SpectralTopology/ActualSpectralWhitening.positive_hermitian_sqrt_contDiffAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ashwin Nayak and Pranab Sen (2007). *Invertible Quantum Operations and Perfect Encryption of Quantum States*. DOI: [10.26421/QIC7.1-2-6](https://doi.org/10.26421/QIC7.1-2-6).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

At every positive definite Hermitian matrix, the actual CFC square root is smooth as a map from the real Hermitian subspace to the original complex matrix space. The derivative of the square map at its positive square root is the invertible Jordan operator V ↦ YV + VY. The local inverse theorem gives a smooth local inverse; uniqueness identifies that inverse with the CFC square root. This identification is the retained escape witness, with audit issue #18787 unfinished and zero validated registrations.

**Theorem 1.2 (support range).**

Lean statement: `D5/S3/SpectralTopology/ActualSpectralWhitening.support_range`

*Proof.* Machine-checked in Lean as `D5/S3/SpectralTopology/ActualSpectralWhitening.support_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ashwin Nayak and Pranab Sen (2007). *Invertible Quantum Operations and Perfect Encryption of Quantum States*. DOI: [10.26421/QIC7.1-2-6](https://doi.org/10.26421/QIC7.1-2-6).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

For every positive semidefinite complex matrix, the actual spectral support has the same complex linear range as the matrix, is Hermitian and is idempotent. The proof uses CFC multiplication and the zero-on-kernel support function. This consumed algebraic helper carries no separate mathematical novelty claim.

**Theorem 1.3 (actual constant rank support smooth).**

Lean statement: `D5/S3/SpectralTopology/ActualSpectralWhitening.actual_constant_rank_support_smooth`

*Proof.* Machine-checked in Lean as `D5/S3/SpectralTopology/ActualSpectralWhitening.actual_constant_rank_support_smooth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ashwin Nayak and Pranab Sen (2007). *Invertible Quantum Operations and Perfect Encryption of Quantum States*. DOI: [10.26421/QIC7.1-2-6](https://doi.org/10.26421/QIC7.1-2-6).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

For an arbitrary smooth family of positive semidefinite complex matrices on an arbitrary real manifold with fixed original model with corners and constant natural rank, the actual spectral support varies smoothly. Locally, an independent family of actual columns gives the Gram projection C(C* C)⁻¹C*. Its range and orthogonal-projection identities identify it with spectralSupport. Rank zero and empty bases are retained.

**Theorem 1.4 (positive matrix sqrt smooth).**

Lean statement: `D5/S3/SpectralTopology/ActualSpectralWhitening.positive_matrix_sqrt_smooth`

*Proof.* Machine-checked in Lean as `D5/S3/SpectralTopology/ActualSpectralWhitening.positive_matrix_sqrt_smooth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ashwin Nayak and Pranab Sen (2007). *Invertible Quantum Operations and Perfect Encryption of Quantum States*. DOI: [10.26421/QIC7.1-2-6](https://doi.org/10.26421/QIC7.1-2-6).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

Every smooth family of positive definite complex matrices has a smooth actual CFC square root. Projection to the real Hermitian subspace and the positive square-root local-inverse theorem give smoothness at every base point. No differentiable spectral decomposition or extra regularity premise is assumed.

**Theorem 1.5 (actual whitening extension).**

Lean statement: `D5/S3/SpectralTopology/ActualSpectralWhitening.actual_whitening_extension`

*Proof.* Machine-checked in Lean as `D5/S3/SpectralTopology/ActualSpectralWhitening.actual_whitening_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ashwin Nayak and Pranab Sen (2007). *Invertible Quantum Operations and Perfect Encryption of Quantum States*. DOI: [10.26421/QIC7.1-2-6](https://doi.org/10.26421/QIC7.1-2-6).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

For a positive semidefinite matrix Q, write P = spectralSupport(Q) and H = Q + identity − P. The matrix H is positive definite. The original zero-on-kernel inverse square root is P(sqrt(H))⁻¹, and the original CFC square root is P sqrt(H). Scalar spectral identities, transported through the actual CFC, prove both equalities.

**Theorem 1.6 (actual constant rank whitening smooth).**

Lean statement: `D5/S3/SpectralTopology/ActualSpectralWhitening.actual_constant_rank_whitening_smooth`

*Proof.* Machine-checked in Lean as `D5/S3/SpectralTopology/ActualSpectralWhitening.actual_constant_rank_whitening_smooth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ashwin Nayak and Pranab Sen (2007). *Invertible Quantum Operations and Perfect Encryption of Quantum States*. DOI: [10.26421/QIC7.1-2-6](https://doi.org/10.26421/QIC7.1-2-6).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

For every smooth constant-rank positive semidefinite matrix family, its actual support, zero-on-kernel inverse square root, and CFC square root are smooth on the original manifold. Local Gram coordinates give the smooth support; the extension H = Q + identity − P is smooth and positive definite. Composing the actual positive square root with matrix inversion and multiplication gives both spectral functions. The live local-inverse identification is reused by this endpoint. All dimensions and ranks remain arbitrary natural numbers, including zero.

## References

- Truth anchor: `D5/S3/SpectralTopology/ActualSpectralWhitening.actual_constant_rank_support_smooth`
- Truth anchor: `D5/S3/SpectralTopology/ActualSpectralWhitening.actual_constant_rank_whitening_smooth`
- Truth anchor: `D5/S3/SpectralTopology/ActualSpectralWhitening.actual_whitening_extension`
- Truth anchor: `D5/S3/SpectralTopology/ActualSpectralWhitening.positive_hermitian_sqrt_contDiffAt`
- Truth anchor: `D5/S3/SpectralTopology/ActualSpectralWhitening.positive_matrix_sqrt_smooth`
- Truth anchor: `D5/S3/SpectralTopology/ActualSpectralWhitening.support_range`
- Dependency: [D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative](../Geometry/AlphaGeometry/HermitianCubeDerivative.md)
- Dependency: [D5/S3/Geometry/ProjectionRange/Prebundle](../Geometry/ProjectionRange/Prebundle.md)
- Dependency: [D5/S3/Quantum/Recovery/SpectralTransposeRecovery](../Quantum/Recovery/SpectralTransposeRecovery.md)
