# Positive polynomial derivative-layer Gramian

## Abstract

Positive polynomial derivative-layer Gramian

**Theorem 1.1 (Positive polynomial derivative-layer Gramian).**

$$\forall x\in U, x\neq 0 \Rightarrow 0<\langle x,H\left(x\right)\rangle$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/DerivativeLayerGramianPositivity.derivative_layer_gramian_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be an arbitrary finite-dimensional real inner-product space, and W an arbitrary complete real inner-product space. Let B:V→V and C:V→W be arbitrary linear maps. Neither observability of the whole V nor a positive dimension is assumed.

Put n=dim V, N(j)=the intersection of ker(C B^k) for 0≤k<j, U=N(n) orthogonal complement, E(j)=N(j) intersect N(j+1) orthogonal complement for 0≤j<n. Pi(j):V→V is the actual orthogonal projection onto E(j). All n layer indices are retained, even when their layer is zero. Write b and c for the continuous linear maps associated to B and C; i:U→V is the inclusion. All norms are induced Hilbert operator norms.

Define A(j)=c composed with b^j composed with Pi(j) composed with i, P(s)=sum over j<n of s^j/j! A(j), and H=the interval integral from zero to one of P(s) adjoint composed with P(s). The integral is the actual operator-valued Bochner interval integral.

The quadratic form of H is strictly positive at every nonzero x in U. In zero dimension this universal assertion is vacuous.

Zero integrated squared polynomial norm implies zero polynomial on the interval. Scalar polynomial coefficient uniqueness makes every A(j)x zero. A projected layer vector then belongs both to N(j+1) and its orthogonal complement; resolving the entire filtration forces x=0.

The finite derivative filtration supplies orthogonal geometry, while the exponential power series and Bochner integral supply the analytic operations.

## References

- Truth anchor: `D5/S3/Observer/Linear/DerivativeLayerGramianPositivity.derivative_layer_gramian_pos`
