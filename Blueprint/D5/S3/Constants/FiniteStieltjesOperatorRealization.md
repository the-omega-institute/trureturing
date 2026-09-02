# Finite Stieltjes Operator Realization

## Abstract

Finite positive atomic Stieltjes moments have positive Hankel truncations and an explicit positive diagonal operator realization.

**Theorem 1.1 (Positive atomic moments generate Hankel and operator positivity).**

$$\begin{gathered}\forall I, \operatorname{Finite}\left(I\right), x, w: I \to \mathbb{R},\\{}(\forall i, 0 \leq x\left(i\right) \land 0 \leq w\left(i\right)) \Rightarrow\\{}(\mu_{n} = \operatorname{sum}\left(i, w\left(i\right) \times x\left(i\right)^{n}\right)), (H_{k}(p, q) = \mu_{p + q}) \Rightarrow\\{}(\forall k, \operatorname{PosSemidef}\left(H_{k}\right) \land \operatorname{q}\left(H_{k}, 0\right) = 0) \land\\{}\exists U: \operatorname{End}\left(\mathbb{R}^{I}\right), v: \mathbb{R}^{I}, (\forall y, 0 \leq \langle U\left(y\right), y\rangle) \land \langle U\left(0\right), 0\rangle = 0 \land\\{}(\forall y, i, U\left(y\right)\left(i\right) = x\left(i\right)y\left(i\right)) \land (\forall n, \mu_{n} = \langle \left(U^{n}\right)\left(v\right), v\rangle).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/FiniteStieltjesOperatorRealization.finite_stieltjes_operator_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let I be finite, and let x and w be nonnegative real node and weight families. Define mu at n as the finite sum of w(i) times x(i) to the n-th power, and define the order-k Hankel matrix by the moment at p+q. Every such truncation is positive semidefinite; its zero coefficient vector explicitly attains equality.

On the real Euclidean space indexed by I, multiplication by x is an explicit diagonal nonnegative operator U. The vector v has coordinates sqrt(w(i)). Every moment is the inner product of U to the n-th power applied to v with v, and the zero state attains equality in operator nonnegativity.

The proof identifies each Hankel truncation with the Gram matrix of the vectors sqrt(w(i)) x(i)^p and applies Mathlib's Gram positivity theorem. It formalizes the unconditional finite positive-atomic core only; no Riemann-hypothesis or square-folded-xi representation is assumed or claimed.

## References

- Truth anchor: `D5/S3/Constants/FiniteStieltjesOperatorRealization.finite_stieltjes_operator_realization`
