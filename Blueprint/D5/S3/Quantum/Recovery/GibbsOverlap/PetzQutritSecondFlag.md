# Complementary-flag overlap bound

## Abstract

A quadratic bound for the complementary effect in the Petz and Gibbs overlap.

**Lemma 1.1 (The matrix representation preserves the logarithm).**

Lean statement: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritSecondFlag.mat_log`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritSecondFlag.mat_log` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a self-adjoint CStarMatrix on a finite index type, mapping its spectral logarithm to the ordinary matrix representation gives the spectral logarithm of the represented matrix.

**Theorem 1.2 (The complementary flag contributes at most a quadratic deficit).**

Lean statement: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritSecondFlag.second_flag_traceNorm_sub_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritSecondFlag.second_flag_traceNorm_sub_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Q be a faithful density matrix on a finite index type and suppose 0 ≤ εM ≤ I/2. Set D = I − εM and Ω = exp(log Q + log D). Then ‖√Ω √D √Q‖₁ − Re Tr Ω ≤ ε² Re Tr(Q M²)/2. Hilbert–Schmidt Hölder and the arithmetic–geometric mean inequality bound the deficit by (Re Tr(DQ) − Re Tr Ω)/2. The Gibbs variational identity and nonnegative relative entropy give Re Tr Ω ≥ 1 + Re Tr(Q log D). Functional calculus lifts log(1 − x) ≥ −x − x² on [0, 1/2] to D.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritSecondFlag.mat_log`
- Truth anchor: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritSecondFlag.second_flag_traceNorm_sub_le`
- Dependency: [D5/S3/Quantum/Divergence/GibbsVariationalIdentity](../../Divergence/GibbsVariationalIdentity.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../../Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/Schatten/Holder](../../Schatten/Holder.md)
