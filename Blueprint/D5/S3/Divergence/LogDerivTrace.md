# Logarithmic Derivative Trace Identity

## Abstract

The trace identity for the integral logarithmic directional derivative.

**Definition 1.1 (Integral logarithmic directional derivative).**

Lean statement: `D5/S3/Divergence/LogDerivTrace.logDeriv`

*Formalization.* `D5/S3/Divergence/LogDerivTrace.logDeriv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a complex square matrix m and direction X, logDeriv m X is the matrix-valued Bochner integral over positive real t of (m + t I)^(-1) X (m + t I)^(-1). The notation D ln in the source paper denotes this integral. This formal statement does not claim that logDeriv is the Frechet derivative of mathlib's Matrix.log; that identification remains outside the available mathlib API tracked by issue #924.

**Theorem 1.2 (Positive definite logarithmic derivative has the direction trace).**

$$\forall m \in \operatorname{PositiveDefinite}\left(\operatorname{Matrix}\left(iota, iota, C\right)\right),\; \forall X \in \operatorname{Hermitian}\left(\operatorname{Matrix}\left(iota, iota, C\right)\right),\; \operatorname{trace}\left(\operatorname{multiply}\left(m, \operatorname{logDeriv}\left(m, X\right)\right)\right) = \operatorname{trace}\left(X\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/LogDerivTrace.trace_mul_logDeriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let m be positive definite and X Hermitian. Unitary spectral decomposition writes each resolvent in the eigenbasis of m. Entrywise inverse-square majorants prove Bochner integrability, and fixed matrix multiplication and trace commute with the integral by finite-dimensional continuity. Trace cyclicity reduces the integrand to a finite sum whose ith scalar kernel is lambda_i/(lambda_i+t)^2. Every lambda_i is positive and the integral of this kernel over positive t is one, leaving the trace of the unitary conjugate of X, hence the trace of X. The Hermitian hypothesis is retained to state the identity on the paper's declared domain.

## References

- Truth anchor: `D5/S3/Divergence/LogDerivTrace.logDeriv`
- Truth anchor: `D5/S3/Divergence/LogDerivTrace.trace_mul_logDeriv`
