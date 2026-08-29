# Multiscale Loewner Constraint

## Abstract

One positive spectrum forces its multiscale budget matrix to be positive semidefinite.

**Theorem 1.1 (A common resolvent spectrum gives a positive semidefinite scale matrix).**

$$\begin{gathered}\forall M: \mathbb{N},\\{}nu: \operatorname{Measure}(\mathbb{R}),\\{}u: \operatorname{Fin}(M) \to \mathbb{R},\\{}(\forall i: \operatorname{Fin}(M), 0 < u_{i}) \land\\{}\operatorname{Injective}(u) \land\\{}(\forall t: \mathbb{R}, 0 < t \Rightarrow \operatorname{Integrable}(xi \mapsto \frac{1}{xi^{2} + t}, nu)) \Rightarrow\\{}\operatorname{let} B: \mathbb{R} \to \mathbb{R} := t \mapsto \operatorname{integral}(nu, xi \mapsto \frac{1}{xi^{2} + t}),\\{}\operatorname{let} L: \operatorname{Matrix}(\operatorname{Fin}(M), \operatorname{Fin}(M), \mathbb{R}) := (i, j) \mapsto \operatorname{if}(i = j, -\operatorname{deriv}(B, u_{i}), \frac{B\left(u_{i}\right) - B\left(u_{j}\right)}{u_{j} - u_{i}}),\\{}\operatorname{PosSemidef}(L).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/MultiscaleLoewnerConstraint.multiscale_loewner_constraint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The measure is the common positive spectrum. Its budget curve and the piecewise divided-difference matrix are both constructed in the displayed proposition, including the derivative diagonal.

Positive scales make every resolvent finite under the stated integrability law. Distinct scales are the domain condition for the off-diagonal quotient in the source formula.

The proof identifies the matrix with the integral Gram kernel. A local half-scale resolvent dominates differentiation under the integral, so the diagonal identity is derived from the same measure.

## References

- Truth anchor: `D5/S3/Weil/Budget/MultiscaleLoewnerConstraint.multiscale_loewner_constraint`
