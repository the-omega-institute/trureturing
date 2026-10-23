# Real Half-Line First Return Moments

## Abstract

The complete real half-line and its finite path have identical endpoint moments before the first boundary return.

**Theorem 1.1 (The first boundary return contributes exactly one).**

$$\forall n \in \mathbb{N}, 1 \leq n \Rightarrow (\forall k \in \mathbb{N}, k < 2n \Rightarrow S_{k}^{n} = S_{k}^{\infty}) \land S_{2n}^{\infty} - S_{2n}^{n} = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/RealL2FirstReturnMoments.endpoint_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be the complete real Hilbert space of square-summable sequences on the positive integers. Its unilateral shift satisfies S e_j = e_(j+1), and K_infinity = 3I-S-S*. Natural coordinate j represents source coordinate j+1. For n at least one, A_n is the n-point path adjacency matrix, K_n = 3I_n-A_n, and b_n is its first coordinate vector. The finite matrix acts on the Euclidean space of n real coordinates. For every natural k, define S_k^(n) to be the real Euclidean inner product of b_n with K_n^k b_n, and S_k^(infinity) to be the real Hilbert inner product of e_1 with K_infinity^k e_1 in H.

Write J_n for extension by zero into H. For k less than n, K_infinity^k e_1 = J_n K_n^k b_n. At order n the infinite iterate has the additional coordinate (-1)^n e_(n+1). Self-adjointness splits an endpoint moment into a pairing of two iterates. Below order 2n at least one factor has not reached the boundary; at order 2n the new coordinate is paired with itself and contributes one.

For a natural n at least one, let hn witness 1 <= n. For the actual carriers, put A_infinity = S + S* on ell2(Nat, Real), A_n = Matrix.toEuclideanCLM(pathAdjacency n) on EuclideanSpace Real (Fin n), e_infinity = endpoint, and e_n = finiteEndpoint n hn. Thus K_X = 3 I_X - A_X for X equal to infinity or n, with the same source-coordinate shift and the original endpoint on each carrier. The scalar adjacency coefficient is defined by $c_{X}(k)$ = $\langle e_{X}, {A_{X}}^{k}(e_{X})\rangle_{\mathbb{R}}$ for every natural k. Since A_X = 3 I_X - K_X, the commuting binomial expansion of A_X^k expresses this coefficient as a linear combination of the K_X endpoint moments of orders zero through k. Applying endpoint_moments, for every natural n at least one and every natural k < 2 n, the finite and infinite adjacency coefficients agree. At k = 2 n all lower-order moment differences vanish, and the coefficient of the order-2 n difference is (-1)^(2 n) = 1. Thus the infinite adjacency coefficient minus the finite one is exactly one. These clauses include k = 0 and n = 1.

For a real time t, define the endpoint-exponential kernel by $M_{X}(t)$ = $\langle e_{X}, \exp(-t K_{X})(e_{X})\rangle_{\mathbb{R}}$. The commuting scalar decomposition -t K_X = -3 t I_X + t A_X gives the displayed scalar factor and the adjacency power series, indexed by every natural k. Here the adjacency operators have nonnegative entries in their coordinate bases. The identities hold for all real times t. For every natural n at least one and every real t, the finite identity is $\operatorname{HasSum}((k: \mathbb{N}) \mapsto \exp(-3t) \cdot \frac{{t}^{k}}{k!} \cdot c_{n}(k), M_{n}(t))$; for every real t, the complete real ell2 identity is $\operatorname{HasSum}((k: \mathbb{N}) \mapsto \exp(-3t) \cdot \frac{{t}^{k}}{k!} \cdot c_{\infty}(k), M_{\infty}(t))$. In the first formula the carrier is exactly EuclideanSpace Real (Fin n) with finiteEndpoint n hn; in the second it is the complete real ell2(Nat, Real) carrier with endpoint. The identities follow by factoring the scalar exponential from the commuting operator exponential and applying the exponential power-series identity to the real endpoint pairing.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/RealL2FirstReturnMoments.endpoint_moments`
