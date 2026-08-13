# Nonnegativity of the Log-Determinant Divergence

## Abstract

The log-determinant divergence is nonnegative on invertible positive semidefinite complex matrices, by reduction to a positive spectral sum.

This theorem closes an open left by the frozen log-determinant module. That module identified its own missing step precisely: "The spectral nonnegativity theorem is NOT proved here; the remaining blocker is the similarity/spectral identification of `sigma^{-1} * rho` with a Hermitian positive-definite congruence (and the resulting trace/determinant eigenvalue sum)." The proof below performs exactly that identification.

**Theorem 1.1 (Log-det divergence is nonnegative on invertible positive semidefinite matrices).**

$$\begin{gathered}\forall n\ [\operatorname{Fintype}(n)] [\operatorname{DecidableEq}(n)],\\\forall \rho, \sigma: \operatorname{Matrix}(n, n, \mathbb{C}),\\(\operatorname{PosSemidef}(\rho) \land \operatorname{IsUnit}(\rho) \land \operatorname{PosSemidef}(\sigma) \land \operatorname{IsUnit}(\sigma)) \Rightarrow\\0\le \operatorname{logDetDivergence}(\rho, \sigma).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/LogDetDivergenceNonneg.logDetDivergence_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement uses positive semidefiniteness together with invertibility for both rho and sigma. For a positive semidefinite matrix, mathlib identifies this conjunction with positive definiteness, and the proof makes that conversion immediately. This is a convenient equivalent interface, not a weakening of the positive-definite hypothesis.

Let s be the positive semidefinite square root of sigma and set A equal to s inverse times rho times s inverse. Since s is Hermitian and invertible, A is a congruence of rho and is therefore positive definite. The identity sigma inverse times rho equals s inverse times A times s then exhibits the matrix in the divergence as similar to A. Cyclicity of trace and multiplicativity of determinant consequently identify its real trace and the real part of its determinant with those of A, in the same convention used by the frozen definition.

Because A is Hermitian positive definite, all of its eigenvalues lambda_i are strictly positive, their sum is its trace, and their product is its determinant. The divergence is therefore the finite sum of lambda_i - log lambda_i - 1. Each summand is nonnegative by the scalar inequality log x <= x - 1 for x > 0, which proves the result.

No equality characterization is claimed. Proving that vanishing forces rho and sigma to coincide would additionally require the strictness condition for log x <= x - 1 and the fact that a Hermitian matrix whose eigenvalues are all one is the identity; that further argument was deliberately not attempted here.

The authored display is legal because no pinned projectable statement fixture exists for this declaration; construction records the resulting ProjectionGap.

## References

- Truth anchor: `D5/S3/Resource/LogDetDivergenceNonneg.logDetDivergence_nonneg`
- Dependency: [D5/S3/Resource/LogDetDivergence](LogDetDivergence.md)
