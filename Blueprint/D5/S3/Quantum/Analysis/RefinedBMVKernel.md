# The coefficient kernel with a positive center

## Abstract

The coefficient kernel with a positive center

**Theorem 1.1 (The coefficient kernel with a positive center).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMVKernel.kernel_pos_psd`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMVKernel.kernel_pos_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With a zero among the remaining entries, the Schur complement reduces the coefficient matrix to a two-dimensional inequality. The zero-center case comes from a Cauchy kernel.

**Theorem 1.2 (Positivity of the symmetric coefficient kernel).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMVKernel.symmetricKernel_psd`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMVKernel.symmetricKernel_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each centered coefficient matrix is positive semidefinite for an arbitrary finite list of nonnegative eigenvalues. A positive center uses the sum of a rank-one matrix and a Cauchy congruence. At a zero center the rank-one term vanishes.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMVKernel.kernel_pos_psd`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMVKernel.symmetricKernel_psd`
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMVCoefficients](RefinedBMVCoefficients.md)
