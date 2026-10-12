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

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/RealL2FirstReturnMoments.endpoint_moments`
