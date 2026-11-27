# Ball Model

## Abstract

Ball Model

Ball model for signature (1,n-1): periods, polarisation, linearised action at fixed points.

**Theorem 1.1 (exists_ball_family).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/BallModel.exists_ball_family`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/BallModel.exists_ball_family` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Some analytic family, parametrising points A(q) with A(0) = o, meets every point with frame o.x. If z : o·(g,α) ≅ o at level K(𝔑), z separable, o.reflection = eigenReflection True z μ, then z : A(q)·(g,α) ≅ A(Kq) near 0, K linear, localTerm(t) = localTerm(0)·det(1 − tK).

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/BallModel.exists_ball_family`
- Dependency: [D5/S3/Zeros/GRH/Lib/Shimura/Transfer/MarkedPairs](../Transfer/MarkedPairs.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/ModelAlongArc](ModelAlongArc.md)
