# Density-matrix kernels and continuity

## Abstract

An integrable common bound and continuity of subentropy on the full density-matrix domain.

All finite dimensions are allowed. Matrices are positive semidefinite with complex trace one. Their real eigenvalues are nonnegative and sum to one. Unitary diagonalization gives det(I+A/t) as the product of 1+lambda_i/t, so the determinant has positive real part whenever t>0.

**Theorem 1.1 (A dimension-independent bound).**

Lean statement: `D5/S3/Quantum/Subentropy/DensityKernel.density_kernel_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/DensityKernel.density_kernel_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

The determinant kernel is nonnegative and at most 1/(1+t)^2 for every positive t and every density matrix. The estimate follows from the sharper classical vertex bound after spectral reduction. It includes repeated eigenvalues and zero eigenvalues.

**Theorem 1.2 (Absolute integrability).**

Lean statement: `D5/S3/Quantum/Subentropy/DensityKernel.integrable_subentropy_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/DensityKernel.integrable_subentropy_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

The continuous kernel on the positive half-line is dominated in absolute value by the common integrable inverse-square function. Hence its defining subentropy integral is absolutely convergent.

**Theorem 1.3 (Continuity at all density matrices).**

Lean statement: `D5/S3/Quantum/Subentropy/DensityKernel.continuousOn_matrixSubentropy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/DensityKernel.continuousOn_matrixSubentropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

The determinant is continuous in the entries, and its real part remains positive on the density domain at each positive t. Dominated convergence with the common function 1/(1+t)^2 gives continuity of Q on the full set of positive trace-one matrices, including its boundary.

## References

- Truth anchor: `D5/S3/Quantum/Subentropy/DensityKernel.continuousOn_matrixSubentropy`
- Truth anchor: `D5/S3/Quantum/Subentropy/DensityKernel.density_kernel_bounds`
- Truth anchor: `D5/S3/Quantum/Subentropy/DensityKernel.integrable_subentropy_kernel`
- Dependency: [D5/S3/Quantum/Subentropy/KernelBounds](KernelBounds.md)
- Dependency: [D5/S3/Quantum/Subentropy/UniformIntegrals](UniformIntegrals.md)
