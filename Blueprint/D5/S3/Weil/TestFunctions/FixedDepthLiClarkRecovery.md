# Fixed-Depth Li-Clark Recovery

## Abstract

Fixed-order Li-coefficient recovery controls the associated finite Toeplitz operator and its smallest eigenvalue.

**Theorem 1.1 (Fixed-depth Li-Clark recovery).**

$$\forall N \in \mathbb{N}, lambda \in \mathbb{N} \to \mathbb{R}, lambdahat \in \mathbb{R} \to \left(\mathbb{N} \to \mathbb{R}\right),\; \left(\left(\left(\left(\left(\left(\left(\operatorname{let} c = (r \mapsto \frac{lambda\left(\operatorname{natAbs}\left(r + 1\right)\right) - 2 \cdot lambda\left(\operatorname{natAbs}\left(r\right)\right) + lambda\left(\operatorname{natAbs}\left(r - 1\right)\right)}{2 \cdot lambda\left(1\right)}) \land \operatorname{let} chat = (L \mapsto (r \mapsto \frac{lambdahat\left(L\right)\left(\operatorname{natAbs}\left(r + 1\right)\right) - 2 \cdot lambdahat\left(L\right)\left(\operatorname{natAbs}\left(r\right)\right) + lambdahat\left(L\right)\left(\operatorname{natAbs}\left(r - 1\right)\right)}{2 \cdot lambda\left(1\right)}))\right) \land \operatorname{let} eta = (L \mapsto \operatorname{exp}\left(-L\right) \cdot L^{N-1})\right) \land \left(\forall r \in \mathbb{Z},\; \operatorname{natAbs}\left(r\right) \le N \Rightarrow \operatorname{IsBigOAtTop}\left((L \mapsto c\left(r\right) - chat\left(L, r\right)), eta\right)\right)\right) \land \operatorname{let} T = \operatorname{Matrix}\left((j,k\in\operatorname{Fin}\left(N+1\right) \mapsto c\left(j - k\right))\right)\right) \land \operatorname{let} That = (L \mapsto \operatorname{Matrix}\left((j,k\in\operatorname{Fin}\left(N+1\right) \mapsto chat\left(L, j - k\right))\right))\right) \land \operatorname{let} hT = \operatorname{curvatureHermitian}\left(lambda\right): \operatorname{IsHermitian}\left(T\right)\right) \land \operatorname{let} hThat = (L \mapsto \operatorname{curvatureHermitian}\left(lambdahat\left(L\right)\right)): \forall L \in \mathbb{R},\; \operatorname{IsHermitian}\left(That\left(L\right)\right)\right) \Rightarrow \left(\left(\operatorname{IsBigOAtTop}\left((L \mapsto \operatorname{opNorm}\left(T - That\left(L\right)\right)), eta\right) \land \operatorname{IsBigOAtTop}\left((L \mapsto \operatorname{lambdaMin}\left(That\left(L\right), hThat\left(L\right)\right) - \operatorname{lambdaMin}\left(T, hT\right)), eta\right)\right) \land \operatorname{TendstoAtTop}\left((L \mapsto \operatorname{lambdaMin}\left(That\left(L\right), hThat\left(L\right)\right)), \operatorname{lambdaMin}\left(T, hT\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/FixedDepthLiClarkRecovery.fixed_depth_li_clark_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The true and windowed Li-Clark moments are constructed from the supplied Li-coefficient sequences by the normalized second-difference formula, and the finite Toeplitz matrices are constructed entry by entry from those moments.

A fixed-order exponential recovery premise for every moment visible at depth N transfers through a finite matrix-basis sum to the L2 operator norm.

The Hermitian Rayleigh characterization bounds the smallest-eigenvalue error by the same operator norm. Exponential-polynomial decay then gives the displayed convergence.

## References

- Truth anchor: `D5/S3/Weil/TestFunctions/FixedDepthLiClarkRecovery.fixed_depth_li_clark_recovery`
