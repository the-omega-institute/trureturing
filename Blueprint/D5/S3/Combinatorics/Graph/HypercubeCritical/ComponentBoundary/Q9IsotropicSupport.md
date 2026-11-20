# Reduction of a supported eigenspace

## Abstract

Reduction of supported eigenvectors at an eigenvalue divisible by a prime

**Theorem 1.1 (A nonzero real supported eigenvector forces a modular kernel vector).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicSupport.exists_zmod_kernel_supported_of_real_eigenvector`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicSupport.exists_zmod_kernel_supported_of_real_eigenvector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restrict the integer matrix after subtracting the eigenvalue to the columns in the prescribed support. If its reduction were injective, a linear left inverse over the prime field could be lifted to an integer matrix. The square product would have determinant congruent to one and would remain injective over the reals.

The real eigenvector rules out this injectivity. When the eigenvalue is divisible by the prime, the resulting nonzero modular vector is killed by the original operator and remains supported within the prescribed set.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicSupport.exists_zmod_kernel_supported_of_real_eigenvector`
