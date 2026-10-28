# Hilbert moment coercivity

## Abstract

Hilbert moment coercivity

**Theorem 1.1 (Positive definiteness of the Hilbert moment matrix).**

$$\forall N\in \mathbb{N}, PosDef\left(H\left(N\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/HilbertMomentCoercivity.hilbertMoment_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For N≥0, let H(N) be the real (N+1) by (N+1) matrix with entry 1/(i+j+1), indexed by 0≤i,j≤N. Let lambda(N) be the minimum of its real eigenvalues.

Its quadratic form is the integral on [0,1] of the squared scalar polynomial with the supplied coefficient vector. A zero integral forces this continuous nonnegative function to vanish. A polynomial vanishing on an interval has all coefficients zero, which proves strict positivity on every nonzero coefficient vector.

**Theorem 1.2 (Hilbert-valued coefficient energy).**

$$\forall W, [RealInnerProductSpace\left(W\right)], \forall N\in \mathbb{N}, \forall v: Fin(N+1)\to W, 0< \lambda\left(N\right) \land \lambda\left(N\right)\sum_{i=0}^{N}\left\lVert v\left(i\right) \right\rVert^{2}\le \int_{0}^{1}\left\lVert \sum_{i=0}^{N}s^{i}v\left(i\right) \right\rVert^{2} \mathrm{d}s$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/HilbertMomentCoercivity.hilbert_polynomial_coercivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let W be any real inner-product space and v(0),...,v(N) arbitrary vectors. There is no ambient dimension or completeness assumption. Expanding the integral gives the entrywise pairing of H(N) with the Gram matrix of these vectors.

The matrix H(N)-lambda(N)I is positive semidefinite. Its Hadamard product with the coefficient Gram matrix is positive semidefinite; testing the all-ones vector yields the energy floor. Thus the same least eigenvalue works in every real Hilbert output space.

**Theorem 1.3 (Factorial short-window scaling).**

$$\forall K, W, [RCLike\left(K\right)] [InnerProductSpace\left(K, W\right)], \forall N\in \mathbb{N}, \forall v: Fin(N+1)\to W, \forall T, 0< T\le 1\Rightarrow \frac{\lambda\left(N\right)T^{2N+1}}{(N!)^{2}}\sum_{i=0}^{N}\left\lVert v\left(i\right) \right\rVert^{2}\le \int_{0}^{T}\left\lVert \sum_{i=0}^{N}\frac{t^{i}}{i!}v\left(i\right) \right\rVert^{2} \mathrm{d}t$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/HilbertMomentCoercivity.taylor_polynomial_energy_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be the real or complex field, W any inner-product space over K, and 0<T≤1. Real coefficients act through the canonical embedding into K. The underlying real inner product preserves all norms.

After t=Ts, the coefficients become T^i v(i)/i!. Since 0<T≤1 and i≤N, each T^i/i! is at least T^N/N!. The unit-interval floor and the change of variable give precisely T^(2N+1)/(N!)^2, including N=0 and T=1.

## References

- Truth anchor: `D5/S3/Observer/Linear/HilbertMomentCoercivity.hilbertMoment_posDef`
- Truth anchor: `D5/S3/Observer/Linear/HilbertMomentCoercivity.hilbert_polynomial_coercivity`
- Truth anchor: `D5/S3/Observer/Linear/HilbertMomentCoercivity.taylor_polynomial_energy_floor`
