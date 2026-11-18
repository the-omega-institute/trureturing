# Finite spectral support decompositions and positive matrix power limits

## Abstract

Finite spectral support decompositions and positive matrix power limits

**Theorem 1.1 (Spectral functions on an eigenmatrix).**

Lean statement: `D5/S3/Quantum/Hiai/SupportPowerLimits.cfc_eigenmatrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/SupportPowerLimits.cfc_eigenmatrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2026). *Log-majorizations between quasi-geometric type means for matrices*. DOI: [10.1016/j.laa.2026.01.003](https://doi.org/10.1016/j.laa.2026.01.003). URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

For arbitrary finite rectangular complex matrices, if A is Hermitian and A V equals V times the real diagonal lambda, then its spectral function f acts on V as the diagonal f of lambda. No continuity assumption on f is required on a finite spectrum.

**Theorem 1.2 (Shifted powers on the support).**

Lean statement: `D5/S3/Quantum/Hiai/SupportPowerLimits.support_rpow_shift_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/SupportPowerLimits.support_rpow_shift_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2026). *Log-majorizations between quasi-geometric type means for matrices*. DOI: [10.1016/j.laa.2026.01.003](https://doi.org/10.1016/j.laa.2026.01.003). URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

For a positive semidefinite matrix A and every nonzero real exponent q, the CFC function that is zero on the zero eigenspace and equals (x plus epsilon) to q elsewhere converges to A to q as positive epsilon tends to zero. This includes negative exponents.

**Theorem 1.3 (The complementary support projection).**

Lean statement: `D5/S3/Quantum/Hiai/SupportPowerLimits.kernel_projection_data`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/SupportPowerLimits.kernel_projection_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2026). *Log-majorizations between quasi-geometric type means for matrices*. DOI: [10.1016/j.laa.2026.01.003](https://doi.org/10.1016/j.laa.2026.01.003). URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

For a positive semidefinite matrix A whose kernel is contained in the kernel of B, Q equals I minus the spectral support of A. It is selfadjoint, idempotent and positive semidefinite, and both A Q and B Q vanish.

**Theorem 1.4 (Real powers on an eigenspace).**

Lean statement: `D5/S3/Quantum/Hiai/SupportPowerLimits.rpow_on_eigenmatrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/SupportPowerLimits.rpow_on_eigenmatrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2026). *Log-majorizations between quasi-geometric type means for matrices*. DOI: [10.1016/j.laa.2026.01.003](https://doi.org/10.1016/j.laa.2026.01.003). URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

For a positive semidefinite matrix X, if X V equals c times V, then X to real exponent q times V equals c to q times V. The scalar and matrix powers use the same totalized real-power convention.

**Theorem 1.5 (Spectral formula for a positive shift).**

Lean statement: `D5/S3/Quantum/Hiai/SupportPowerLimits.shifted_rpow_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/SupportPowerLimits.shifted_rpow_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2026). *Log-majorizations between quasi-geometric type means for matrices*. DOI: [10.1016/j.laa.2026.01.003](https://doi.org/10.1016/j.laa.2026.01.003). URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

For a positive semidefinite matrix A and positive epsilon, the real power of A plus epsilon I is the CFC function (x plus epsilon) to q on the fixed spectrum of A.

**Theorem 1.6 (The support and kernel parts of a shift).**

Lean statement: `D5/S3/Quantum/Hiai/SupportPowerLimits.inverse_shift_split`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/SupportPowerLimits.inverse_shift_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2026). *Log-majorizations between quasi-geometric type means for matrices*. DOI: [10.1016/j.laa.2026.01.003](https://doi.org/10.1016/j.laa.2026.01.003). URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

For every real exponent q, the power of A plus positive epsilon I splits into its support-restricted CFC power and epsilon to q times the complementary support projection. The identity is valid for singular A and negative q.

**Theorem 1.7 (Continuity of positive powers).**

Lean statement: `D5/S3/Quantum/Hiai/SupportPowerLimits.tendsto_positive_rpow`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/SupportPowerLimits.tendsto_positive_rpow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2026). *Log-majorizations between quasi-geometric type means for matrices*. DOI: [10.1016/j.laa.2026.01.003](https://doi.org/10.1016/j.laa.2026.01.003). URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

For a net of eventually positive semidefinite matrices converging to a positive semidefinite M, every strictly positive real power converges to the same power of M. The filter and finite matrix dimension are arbitrary.

**Theorem 1.8 (Composition of finite spectral real powers).**

Lean statement: `D5/S3/Quantum/Hiai/SupportPowerLimits.psd_nested_rpow`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/SupportPowerLimits.psd_nested_rpow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2026). *Log-majorizations between quasi-geometric type means for matrices*. DOI: [10.1016/j.laa.2026.01.003](https://doi.org/10.1016/j.laa.2026.01.003). URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

For a positive semidefinite A and real p and q, the iterated real power (A to p) to q equals A to p times q. The scalar real-power identity is applied on the nonnegative finite spectrum.

**Theorem 1.9 (Continuity of positive trace powers).**

Lean statement: `D5/S3/Quantum/Hiai/SupportPowerLimits.tendsto_tracePower`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/SupportPowerLimits.tendsto_tracePower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2026). *Log-majorizations between quasi-geometric type means for matrices*. DOI: [10.1016/j.laa.2026.01.003](https://doi.org/10.1016/j.laa.2026.01.003). URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

Under eventual positive semidefiniteness and convergence to a positive semidefinite matrix, the real trace of every strictly positive matrix power converges. This combines positive-power continuity with the continuous real trace.

## References

- Truth anchor: `D5/S3/Quantum/Hiai/SupportPowerLimits.cfc_eigenmatrix`
- Truth anchor: `D5/S3/Quantum/Hiai/SupportPowerLimits.inverse_shift_split`
- Truth anchor: `D5/S3/Quantum/Hiai/SupportPowerLimits.kernel_projection_data`
- Truth anchor: `D5/S3/Quantum/Hiai/SupportPowerLimits.psd_nested_rpow`
- Truth anchor: `D5/S3/Quantum/Hiai/SupportPowerLimits.rpow_on_eigenmatrix`
- Truth anchor: `D5/S3/Quantum/Hiai/SupportPowerLimits.shifted_rpow_formula`
- Truth anchor: `D5/S3/Quantum/Hiai/SupportPowerLimits.support_rpow_shift_tendsto`
- Truth anchor: `D5/S3/Quantum/Hiai/SupportPowerLimits.tendsto_positive_rpow`
- Truth anchor: `D5/S3/Quantum/Hiai/SupportPowerLimits.tendsto_tracePower`
- Dependency: [D5/S3/Quantum/Hiai/InverseMeanVariational](InverseMeanVariational.md)
- Dependency: [D5/S3/Quantum/Recovery/SpectralTransposeRecovery](../Recovery/SpectralTransposeRecovery.md)
