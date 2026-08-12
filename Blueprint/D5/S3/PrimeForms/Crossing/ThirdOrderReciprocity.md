# The Third-Order Reciprocity Linear Constitution

## Abstract

Conjugation by the reciprocity matrix K reverses a matrix to its adjugate iff it is trace-orthogonal to K.

**Theorem 1.1 (K conjugates gamma to its adjugate iff gamma is trace-orthogonal to K).**

$$K = \begin{pmatrix}1&-2\\2&-1\end{pmatrix}, K^2 = -3 I\\K \gamma \operatorname{adj} K = 3 \operatorname{adj} \gamma \iff \operatorname{tr}(\gamma K) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Crossing/ThirdOrderReciprocity.k_reversal_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The third-order reciprocity matrix K = [[1,-2],[2,-1]] is an integer 2x2 matrix with det K = 3 and K^2 = -3*I, so it behaves as a square root of -3. For every integer 2x2 matrix gamma, conjugation by K reverses gamma to (det K) times its adjugate — that is, K*gamma*adj(K) = 3*adj(gamma) — exactly when gamma is trace-orthogonal to K, tr(gamma*K) = 0. The adjugate form is inverse-free, so the identity holds for all gamma including singular ones (for invertible gamma, adj(gamma) = det(gamma)*gamma^{-1}).

The trace tr(gamma*K) reduces to the linear form g00 + 2*g01 - 2*g10 - g11. Because K is traceless, the 2x2 Cayley-Hamilton polarization gives K*gamma + gamma*K = (tr gamma)*K + tr(gamma*K)*I, and every entry of K*gamma*adj(K) - 3*adj(gamma) collapses to that same linear form; hence the matrix equation holds iff the trace vanishes. The forward direction reads off entry (0,0); the backward direction checks all four entries.

Mathlib has the adjugate and its 2x2 formula but no statement that conjugation by a specific square-root-of-(-3) matrix equals the adjugate iff trace-orthogonality, so this is a genuine biconditional, not a library restatement. It records only the algebraic linear constitution of residual E.72. The geometric axis biconditional (the rotation axis passing through the reference point), the class-level crossing criterion, the Sarnak reciprocity dictionary, and the Fricke bridge toward X0(3) are not covered.

## References

- Truth anchor: `D5/S3/PrimeForms/Crossing/ThirdOrderReciprocity.k_reversal_iff`
