# Prime Error

## Abstract

Prime Error

Weighted non-split prime sums; their Mellin transform has poles at zeros of L-functions.

**Theorem 1.1 (isPolar_primeError).**

Lean statement: `D5/S3/Zeros/GRH/New/Endgame/PrimeError.isPolar_primeError`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Endgame/PrimeError.isPolar_primeError` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

For d ≡ 7 mod 8 prime to M, v ↦ R_M(e^v) is polar (IsPolar) with residue at s equal to ∑_ξ (ord_s L̃(ξ) − ord_s L̃(ξ(·/d))) / (φ(M) s(1 − s)), ξ over the characters mod M, L̃ = entireL.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Endgame/PrimeError.isPolar_primeError`
- Dependency: [D5/S3/Zeros/GRH/Lib/Analytic/Landau/PolarLandau](../../Lib/Analytic/Landau/PolarLandau.md)
