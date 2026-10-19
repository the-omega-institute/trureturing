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

The public declarations diagonal_operator_nonnegative and moment_eq_operator_pairing retain the specified diagonal operator and rootWeightVector. For the scalar input map J(u)=u v, the adjoint identity gives J* U^k J=mu(k) id for every k. Coordinatewise multiplication by real nodes is symmetric, so nonnegative quadratic pairings give a positive operator. The finite-prefix error is the maximum of the absolute moment differences over k from zero through the chosen prefix length.

These finite atomic realizations also exhibit discontinuity of exact prefix criteria. For epsilon>0, the prefix (1,1,1,1+epsilon) has positive Hankel blocks and ordinary ranks both equal to one. A symmetric realization would force C J(1)=J(1) from its first three moments, contradicting its fourth moment. It approaches the unit atom at node one. For weights (1-delta,delta) at nodes (1,2), with 0<delta<1, the moments are 1+delta(2^k-1). Every fixed prefix approaches the unit atom, while the order-one Hankel determinant is delta(1-delta)>0. The explicit two-dimensional realization and the Gram rank lower bound give minimum dimension two, compared with one at the limit; both spectra lie in [1,2].

Without a common spectral upper bound, fix any natural r and set t=n+2. Use nodes (1,t^2) and weights (1-w,w), where w=1/t^(4r+3). Both weights are positive. Uniformly for k<=2r+1, the absolute difference of the k-th moment from one is at most 1/t. The next moment equals 1-w+t and tends to positive infinity. For r>=2, the two distinct nodes and positive weights make the ordinary Hankel ranks at orders r and r-1 both equal to two. These are consequences of the finite atomic suppliers, adjoint and Gram rank identities, and scalar estimates; they introduce no further representation assumption.

## References

- Truth anchor: `D5/S3/Constants/FiniteStieltjesOperatorRealization.finite_stieltjes_operator_realization`
