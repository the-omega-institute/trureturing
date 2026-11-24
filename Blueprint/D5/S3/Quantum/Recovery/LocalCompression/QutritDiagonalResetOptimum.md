# Exact optimum for pure diagonal-reset qutrit compression

## Abstract

The pure qutrit Bell-source trace-distance minimum for diagonal-reset compression through a qubit.

**Theorem 1.1 (An exact rational bracket for the stationary amplitude).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/QutritDiagonalResetOptimum.exists_stationary_characteristic`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/QutritDiagonalResetOptimum.exists_stationary_characteristic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kohtaro Kato (2025). *Exact and Local Compression of Quantum Bipartite States*. DOI: [10.1109/TIT.2025.3562884](https://doi.org/10.1109/TIT.2025.3562884). URL: <https://arxiv.org/abs/2309.07434>.

*Commentary.*

The accompanying isotropic-compression manuscript supplies the stationary characteristic-polynomial certificate. Solve the stationarity equation for the spectral parameter and substitute the resulting rational function into the characteristic polynomial. Its denominator is negative throughout the closed interval with endpoints 0.80680296 and 0.80680298. Exact rational signs at the endpoints give an interior zero by continuity. At the resulting spectral parameter, the quartic Taylor identity gives a strictly negative determinant at every other amplitude in [0, 1].

**Theorem 1.2 (The pure reset and two-Kraus decoder attain the minimum).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/QutritDiagonalResetOptimum.pure_diagonal_reset_optimum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/QutritDiagonalResetOptimum.pure_diagonal_reset_optimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kohtaro Kato (2025). *Exact and Local Compression of Quantum Bipartite States*. DOI: [10.1109/TIT.2025.3562884](https://doi.org/10.1109/TIT.2025.3562884). URL: <https://arxiv.org/abs/2309.07434>.

*Commentary.*

The first two pivots of the shifted matched block are positive at the stationary root, and its residual Schur complement vanishes. The resulting positive semidefinite form bounds every unit-vector expectation. A strictly larger shift than the greatest expectation would be positive definite and would have positive determinant. At every other amplitude the negative determinant instead forces a strictly larger Rayleigh maximum. The retained Rayleigh attainment theorem and diagonal-reset converse transfer these comparisons to half the joint trace norm. The strict comparison identifies the unique attenuation amplitude within the explicit family. The channel comparison quantifies over plane-preserving diagonal resets and arbitrary qubit-to-qutrit decoders at the pure endpoint.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/QutritDiagonalResetOptimum.exists_stationary_characteristic`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/QutritDiagonalResetOptimum.pure_diagonal_reset_optimum`
- Dependency: [D5/S3/Quantum/Recovery/LocalCompression/QutritDiagonalResetDistortion](QutritDiagonalResetDistortion.md)
