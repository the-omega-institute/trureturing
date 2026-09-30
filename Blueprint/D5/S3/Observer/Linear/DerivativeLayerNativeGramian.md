# Invertible physical scaling and native Gramian limit

## Abstract

Invertible physical scaling and native Gramian limit

**Theorem 1.1 (Invertible physical scaling and native Gramian limit).**

$$(\forall 0<T, d\left(T\right)e\left(T\right)=I_{U} \land e\left(T\right)d\left(T\right)=I_{U} \land e\left(T\right)G\left(T\right)e\left(T\right)=\int_{0}^{1} Z\left(T, s\right)^{*}Z\left(T, s\right) ds)\\{}\land (\forall x\in U,x\neq 0\Rightarrow 0<\langle x,H\left(x\right)\rangle)\\{}\land (\exists R\ge 0, \forall T, (0<T\le 1 \land T\left\lVert b \right\rVert<1) \Rightarrow \left\lVert e\left(T\right)G\left(T\right)e\left(T\right)-H \right\rVert\le RT)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/DerivativeLayerNativeGramian.derivative_layer_native_gramian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be an arbitrary finite-dimensional real inner-product space, and W an arbitrary complete real inner-product space. Let B:V→V and C:V→W be arbitrary linear maps. Neither observability of the whole V nor a positive dimension is assumed.

Put n=dim V, N(j)=the intersection of ker(C B^k) for 0≤k<j, U=N(n) orthogonal complement, E(j)=N(j) intersect N(j+1) orthogonal complement for 0≤j<n. Pi(j):V→V is the actual orthogonal projection onto E(j). All n layer indices are retained, even when their layer is zero. Write b and c for the continuous linear maps associated to B and C; i:U→V is the inclusion. All norms are induced Hilbert operator norms.

On U let Q(j) be Pi(j) restricted to U, with its range returned to U by the orthogonal projection onto U. Put d(T)=sum sqrt(T) T^j Q(j) and e(T)=sum (sqrt(T) T^j)^(-1) Q(j). Define A(t)=c exp(t b) i and G(T)=the interval integral from zero to T of A(t) adjoint composed with A(t).

Put P(s)=sum over j<n of s^j/j! c b^j Pi(j) i and H=the interval integral from zero to one of P(s) adjoint composed with P(s). Write Z(T,s)=sqrt(T) A(T s) e(T). Composition is written by juxtaposition in the display, and a star denotes the Hilbert adjoint.

For every T>0, d(T)e(T) and e(T)d(T) both equal the identity on U, and e(T)G(T)e(T) equals the integral of Z(T,s) adjoint composed with Z(T,s). H has positive quadratic form at every nonzero state. There is R≥0 for which the linear error holds whenever 0<T≤1 and T times the norm of b is less than one.

Projection orthogonality gives the inverse equations without a rank premise. The physical change of variables t=T s and self-adjointness of the scaling give the integral identity. Uniform normalized-trajectory convergence controls the difference of the two squared operators and its integral.

The finite derivative filtration supplies orthogonal geometry, while the exponential power series and Bochner integral supply the analytic operations.

## References

- Truth anchor: `D5/S3/Observer/Linear/DerivativeLayerNativeGramian.derivative_layer_native_gramian`
- Dependency: [D5/S3/Observer/Linear/DerivativeLayerGramianPositivity](DerivativeLayerGramianPositivity.md)
- Dependency: [D5/S3/Observer/Linear/DerivativeLayerNormalizedObservation](DerivativeLayerNormalizedObservation.md)
