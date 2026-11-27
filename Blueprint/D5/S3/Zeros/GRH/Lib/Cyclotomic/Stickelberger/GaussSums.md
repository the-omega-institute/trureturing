# Gauss Sums

## Abstract

Gauss Sums

Valuations of Gauss sums, Jacobi-type quotients, distribution relation up to roots of unity.

**Theorem 1.1 (exists_jacobi_family).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Cyclotomic/Stickelberger/GaussSums.exists_jacobi_family`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Cyclotomic/Stickelberger/GaussSums.exists_jacobi_family` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Stickelberger: for B above p, some J : ℚ/ℤ → ℚ̄^× satisfies, if M ∣ p−1 and Mx = 0: σJ(x) = J(cyc_M(σ)x); J(x) is a unit off p, of order floorDiff c x at B, of absolute value 1 in all complex embeddings; J(x+b)/J(x) ≡ 1 above primes q ∣ p−1 if qb = 0; ∏_{b mod r} J(x+b/r)/J(rx) is a root of unity for r ∣ M prime to c.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Cyclotomic/Stickelberger/GaussSums.exists_jacobi_family`
- Dependency: [D5/S3/Zeros/GRH/Lib/ClassField/Places/LocalBasics](../../ClassField/Places/LocalBasics.md)
