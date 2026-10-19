# Logarithmic Derivative Trace Identity

## Abstract

The trace identity for the integral logarithmic directional derivative.

**Lemma 1.1 (Scalar inverse-square integrability).**

$$\forall (lambda: \mathbb{R}), (0 < lambda) \Rightarrow (\operatorname{IntegrableOn}\left(((t: \mathbb{R}) \mapsto \frac{lambda}{(lambda + t)^{2}}), \operatorname{Set}.\operatorname{Ioi}(0)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/LogDerivTrace.scalarKernel_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive lambda, the function lambda divided by (lambda plus t) squared is integrable on the positive half-line.

**Lemma 1.2 (Paired resolvent integrability).**

$$\forall (a: \mathbb{R}), \forall (b: \mathbb{R}), (0 < a) \Rightarrow ((0 < b) \Rightarrow (\operatorname{IntegrableOn}\left(((t: \mathbb{R}) \mapsto \frac{1}{(a + t) \cdot (b + t)}), \operatorname{Set}.\operatorname{Ioi}(0)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/LogDerivTrace.pairKernel_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a and b, the reciprocal of (a plus t) times (b plus t) is integrable on the positive half-line.

**Lemma 1.3 (The resolvent in the eigenbasis).**

$$\forall (iota: Type), [\operatorname{Fintype}\left(iota\right)] [\operatorname{DecidableEq}\left(iota\right)], \forall (m: \operatorname{Matrix}\left(iota, iota, \mathbb{C}\right)), \forall (hm: \operatorname{PosDef}\left(m\right)), \forall (t: \mathbb{R}), (0 \le t) \Rightarrow ((m + (t) \cdot (1))^{- 1} = hm.\operatorname{isHermitian}.\operatorname{eigenvectorUnitary} \cdot \operatorname{diagonal}\left(((i: iota) \mapsto ((hm.\operatorname{isHermitian}.\operatorname{eigenvalues}(i) + t: \mathbb{C}))^{- 1})\right) \cdot \operatorname{star}\left(hm.\operatorname{isHermitian}.\operatorname{eigenvectorUnitary}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/LogDerivTrace.resolvent_eq_spectral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse of a positive definite matrix plus t times the identity is obtained by taking reciprocal shifted eigenvalues in its unitary eigenbasis, for nonnegative t.

**Lemma 1.4 (Matrix logarithmic derivative integrability).**

$$\forall (iota: Type), [\operatorname{Fintype}\left(iota\right)] [\operatorname{DecidableEq}\left(iota\right)], \forall (m: \operatorname{Matrix}\left(iota, iota, \mathbb{C}\right)), \forall (X: \operatorname{Matrix}\left(iota, iota, \mathbb{C}\right)), (\operatorname{PosDef}\left(m\right)) \Rightarrow (\operatorname{IntegrableOn}\left(((t: \mathbb{R}) \mapsto (m + (t) \cdot (1))^{- 1} \cdot X \cdot (m + (t) \cdot (1))^{- 1}), \operatorname{Set}.\operatorname{Ioi}(0)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/LogDerivTrace.logDeriv_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite m and any complex direction X, the two-resolvent sandwich is Bochner integrable on the positive half-line.

**Definition 1.5 (Integral logarithmic directional derivative).**

Lean statement: `D5/S3/Divergence/LogDerivTrace.logDeriv`

*Formalization.* `D5/S3/Divergence/LogDerivTrace.logDeriv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a complex square matrix m and direction X, logDeriv m X is the matrix-valued Bochner integral over positive real t of (m + t I)^(-1) X (m + t I)^(-1). The notation D ln in the source paper denotes this integral. The declaration does not assert that logDeriv is the Frechet derivative of Matrix.log; the pinned Mathlib API exposes the matrix logarithm through CFC.log and supplies no theorem identifying that derivative with this integral.

**Theorem 1.6 (Positive definite logarithmic derivative has the direction trace).**

$$\forall m \in \operatorname{PositiveDefinite}\left(\operatorname{Matrix}\left(iota, iota, C\right)\right),\; \forall X \in \operatorname{Hermitian}\left(\operatorname{Matrix}\left(iota, iota, C\right)\right),\; \operatorname{trace}\left(\operatorname{multiply}\left(m, \operatorname{logDeriv}\left(m, X\right)\right)\right) = \operatorname{trace}\left(X\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/LogDerivTrace.trace_mul_logDeriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let m be positive definite and X Hermitian. Unitary spectral decomposition writes each resolvent in the eigenbasis of m. Entrywise inverse-square majorants prove Bochner integrability, and fixed matrix multiplication and trace commute with the integral by finite-dimensional continuity. Trace cyclicity reduces the integrand to a finite sum whose ith scalar kernel is lambda_i/(lambda_i+t)^2. Every lambda_i is positive and the integral of this kernel over positive t is one, leaving the trace of the unitary conjugate of X, hence the trace of X. The Hermitian hypothesis is retained to state the identity on the paper's declared domain.

## References

- Truth anchor: `D5/S3/Divergence/LogDerivTrace.logDeriv`
- Truth anchor: `D5/S3/Divergence/LogDerivTrace.logDeriv_integrable`
- Truth anchor: `D5/S3/Divergence/LogDerivTrace.pairKernel_integrable`
- Truth anchor: `D5/S3/Divergence/LogDerivTrace.resolvent_eq_spectral`
- Truth anchor: `D5/S3/Divergence/LogDerivTrace.scalarKernel_integrable`
- Truth anchor: `D5/S3/Divergence/LogDerivTrace.trace_mul_logDeriv`
