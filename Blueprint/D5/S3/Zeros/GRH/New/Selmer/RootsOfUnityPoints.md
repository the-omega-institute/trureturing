# Roots Of Unity Points

## Abstract

Roots Of Unity Points

ℓ-power roots of unity keep valuations of polynomials of any degree low.

**Theorem 1.1 (exists_roots_of_unity_ellVal_le).**

Lean statement: `D5/S3/Zeros/GRH/New/Selmer/RootsOfUnityPoints.exists_roots_of_unity_ellVal_le`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Selmer/RootsOfUnityPoints.exists_roots_of_unity_ellVal_le` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Fix δ > 0, m, L, a, q and finitely many bounds B_k. For large N, then large O: given F_{k,d} (1 ≤ d ≤ m) in ≤ q variables with valuation ≤ B_k at points u_{k,d}, ℓ ∣ (u − 1)^a coordinatewise, and monic D_n of total degree ≤ L, some tuple ζ in O of ℓ^N-th roots of unity has v(F_{k,d}(ζ^d)) ≤ δ + B_k and all v(D_n(ζ_j)) ≤ δ.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Selmer/RootsOfUnityPoints.exists_roots_of_unity_ellVal_le`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/NumberTheory/Valuation](../../Lib/General/NumberTheory/Valuation.md)
