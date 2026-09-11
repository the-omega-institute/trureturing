# Attained Schur Minimum

## Abstract

The Schur quadratic form is the attained minimum over the internal block.

**Theorem 1.1 (Boundary quadratic minimum).**

$$\operatorname{IsLeast}(\{\begin{pmatrix}x\\y\end{pmatrix}^{*}\begin{pmatrix}A&B\\B^{*}&C\end{pmatrix}\begin{pmatrix}x\\y\end{pmatrix} \mid y \in \mathbb{C}^{n}\}, x^{*}(A-BC^{-1}B^{*})x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/SchurMinimum.schur_quadratic_is_least` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite Hermitian block matrix with positive definite internal block C, the set of energies at a fixed boundary vector has the stated least element. It is attained at the negative inverse-block response. The proof applies Mathlib's Schur decomposition and positive-semidefinite quadratic inequality. This is a repository API wrapper of those upstream results.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/SchurMinimum.schur_quadratic_is_least`
