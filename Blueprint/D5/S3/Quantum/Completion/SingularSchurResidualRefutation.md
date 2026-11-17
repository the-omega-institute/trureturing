# Singular Schur residual is insufficient

## Abstract

The singular block with zero old corner and unit cross entry has a nonnegative naive residual but is not positive semidefinite.

Indices are Fin 2 and scalars are complex. The matrix bad is the explicit block [[0,1],[1,1]], and witness is the vector (1,-1). Matrix.PosSemidef requires every complex quadratic form to have nonnegative real part.

**Definition 1.1 (The singular two by two block).**

Lean statement: `D5/S3/Quantum/Completion/SingularSchurResidualRefutation.bad`

*Formalization.* `D5/S3/Quantum/Completion/SingularSchurResidualRefutation.bad` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The old corner is the zero 1 by 1 block, the cross entry is one, and the new diagonal entry is one. It is the concrete boundary matrix from the C129 Schur-complement warning.

**Definition 1.2 (Positive semidefiniteness of the displayed block).**

$$\operatorname{Matrix.PosSemidef}\left(bad\right)$$

*Formalization.* `D5/S3/Quantum/Completion/SingularSchurResidualRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is exactly the tempting conclusion obtained by retaining only the scalar residual q minus b star G pseudoinverse b; the range condition is omitted.

**Theorem 1.3 (The singular block is not positive semidefinite).**

$$\neg (claim)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/SingularSchurResidualRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The vector (1,-1) has quadratic value -1 for bad. The kernel positivity obligation would therefore imply 0 <= -1, which is impossible. This records why the range condition b in Ran G must accompany the nonnegative Schur residual at singular boundaries.

## References

- Truth anchor: `D5/S3/Quantum/Completion/SingularSchurResidualRefutation.bad`
- Truth anchor: `D5/S3/Quantum/Completion/SingularSchurResidualRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Completion/SingularSchurResidualRefutation.result`
