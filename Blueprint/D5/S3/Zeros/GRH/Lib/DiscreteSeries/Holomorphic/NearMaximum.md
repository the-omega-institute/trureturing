# Near Maximum

## Abstract

Near Maximum

Rapidly decreasing holomorphic forms are large only away from cusps, explicit depth.

**Theorem 1.1 (exists_near_max).**

Lean statement: `D5/S3/Zeros/GRH/Lib/DiscreteSeries/Holomorphic/NearMaximum.exists_near_max`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/DiscreteSeries/Holomorphic/NearMaximum.exists_near_max` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let F ≠ 0 be rapidly decreasing, automorphic of level ς = −ς̄, Im Φ_wς ∈ (0,c], c ≥ 1, holomorphic of weight in [−B,B], B ≥ 2, gap 1. Some z has F(z) ≠ 0, |F| ≤ 2|F(z)|, and |F(g)| ≥ |F(z)| implies Space.firstMinimum(g) ≥ (Bc)^{−½}.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/DiscreteSeries/Holomorphic/NearMaximum.exists_near_max`
- Dependency: [D5/S3/Zeros/GRH/Lib/Weil/Lift/Staircase](../../Weil/Lift/Staircase.md)
