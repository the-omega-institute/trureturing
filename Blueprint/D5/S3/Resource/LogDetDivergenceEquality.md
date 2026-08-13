# Equality in the Log-Determinant Divergence

## Abstract

The log-determinant divergence vanishes exactly when its two invertible positive semidefinite matrix arguments coincide.

This theorem completes the pair begun by the preceding nonnegativity wave. That wave deliberately declined the equality case and named its two remaining obstructions: strictness in the scalar inequality log x <= x - 1, and the fact that a Hermitian matrix whose eigenvalues are all one is the identity. Both obstructions are closed here.

**Theorem 1.1 (Zero log-det divergence characterizes equality on invertible positive semidefinite matrices).**

$$\begin{gathered}\forall n\ [\operatorname{Fintype}(n)] [\operatorname{DecidableEq}(n)],\\\forall \rho, \sigma: \operatorname{Matrix}(n, n, \mathbb{C}),\\(\operatorname{PosSemidef}(\rho) \land \operatorname{IsUnit}(\rho) \land \operatorname{PosSemidef}(\sigma) \land \operatorname{IsUnit}(\sigma)) \Rightarrow\\\operatorname{logDetDivergence}(\rho, \sigma)=0 \Leftrightarrow \rho=\sigma.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/LogDetDivergenceEquality.logDetDivergence_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hypotheses are identical, word for word, to those of the frozen nonnegativity theorem: rho and sigma are positive semidefinite and invertible. The two theorems therefore form a complete nonnegativity-plus-equality pair over exactly the same domain.

As in the nonnegativity proof, let s be the positive semidefinite square root of sigma and set A equal to s inverse times rho times s inverse. Similarity and the trace and determinant identities express the divergence as the finite sum of lambda_i - log lambda_i - 1 over the strictly positive eigenvalues of the Hermitian positive-definite matrix A. Every summand is nonnegative, so a vanishing sum forces every summand to vanish.

For an eigenvalue different from one, the strict inequality log x < x - 1 makes its summand strictly positive. Hence every eigenvalue is one. The spectral theorem then reconstructs A as the identity, and unwinding its definition through the square-root identities gives rho equal to sigma. Conversely, equality of rho and sigma reduces the claim to the frozen zero self-divergence theorem.

The Lean module deliberately records the provenance of two negative mathlib searches so that a later reader does not repeat them. There is no declaration `Real.log_lt_sub_one_of_ne`; the available strict result is `Real.log_lt_sub_one_of_pos`. There is likewise no declaration `Matrix.IsHermitian.eq_one_of_eigenvalues_eq_one`; the identity is reconstructed directly from `Matrix.IsHermitian.spectral_theorem`. This record is deliberate rather than incidental.

The authored display is legal because no pinned projectable statement fixture exists for this declaration; construction records the resulting ProjectionGap.

## References

- Truth anchor: `D5/S3/Resource/LogDetDivergenceEquality.logDetDivergence_eq_zero_iff`
- Dependency: [D5/S3/Resource/LogDetDivergenceNonneg](LogDetDivergenceNonneg.md)
