# Finite-Rank Projection Error

## Abstract

Finite-dimensional compression gives a square-summable error with a dimension bound.

**Theorem 1.1 (A dimension bound in every Hilbert basis).**

$$\forall k \in \left\{\mathbb{R}, \mathbb{C}\right\}, E \in \operatorname{Hilbert}\left(k\right), I \in Type, b \in \operatorname{HilbertBasis}\left(I, k, E\right), T \in \operatorname{BoundedLinear}\left(k, E, E\right), K \in \operatorname{FiniteSubspace}\left(k, E\right),\; \begin{aligned}\text{let} m = \operatorname{dim}\left(k, K\right), P = \operatorname{proj}\left(K\right), Q = Id - P, D = T - Q\circ T\circ Q;\\\operatorname{Summable}\left((i:I \mapsto \left\lVert \operatorname{D}\left(\operatorname{b}\left(i\right)\right) \right\rVert^{2})\right) \land \sqrt{\sum_{i\in I}\left\lVert \operatorname{D}\left(\operatorname{b}\left(i\right)\right) \right\rVert^{2}} \le 2 \cdot \sqrt{m} \cdot \left\lVert T \right\rVert\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/FiniteRankProjectionError.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k be the real or complex scalar field, E a complete inner product space over k, I any index type, and b a Hilbert basis of E indexed by I. Let T be any bounded k-linear endomorphism and K a finite-dimensional subspace of E. Write m for the dimension of K, P for the orthogonal projection onto K viewed as an endomorphism, Q=Id-P, and D=T-QTQ. The squared norms of D on the basis are summable, and their sum has square root at most 2 sqrt(m) times the operator norm of T.

Choose an orthonormal basis e of K with m elements. For any bounded endomorphism A, finite-dimensional Parseval expresses the square norm of PA(b(i)) as the sum over j of the squared absolute values of the inner products of b(i) with the adjoint image A*(e(j)). Bessel's inequality makes each coefficient family summable and bounds its sum by the square norm of A*(e(j)). Interchanging the finite sum with the convergent sum over I therefore bounds the total by m times the square of the operator norm of A.

Apply this estimate to A=T and A=Id. The latter gives a bound of m for the sum of the squared norms of P(b(i)); the norm of Id is at most one even on the zero space. The identity D=PT+QTP and the contractivity of Q bound each squared error by twice the sum of the corresponding squared PT term and the squared P term multiplied by the square of the norm of T. This summable majorant has total at most 4m times the square of the norm of T. Taking square roots gives the assertion.

No self-adjointness or Hilbert-Schmidt assumption on T is needed. The index type can be infinite or empty, and m can be zero. When K is zero the error is zero; the proof uses no division by m and no nonzero-dimension hypothesis.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/FiniteRankProjectionError.result`
