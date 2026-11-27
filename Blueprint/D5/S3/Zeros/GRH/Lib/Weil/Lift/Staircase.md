# Staircase

## Abstract

Staircase

Holomorphic Fock vectors and kernels; automorphic functions of a level, basic API. Dictionary between residue-matrix functions, moduli and named Weil data; finite Fourier expansion. A rapidly decreasing function of a level times a theta kernel keeps both properties. Products of minors are joint harmonic highest vectors for (U(p,q), U(n)), Kashiwara–Vergne.

**Theorem 1.1 (staircase_harmonic_highest).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Weil/Lift/Staircase.staircase_harmonic_highest`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Weil/Lift/Staircase.staircase_harmonic_highest` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Staircases: the product of k(η, p) copies of the p × p minor on the first p columns of sign η and the first (η = 1) or last p rows is, if the sizes fit, nonzero, harmonic and highest on both sides, of explicit weights.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Weil/Lift/Staircase.staircase_harmonic_highest`
- Dependency: [D5/S3/Zeros/GRH/Lib/ClassField/HeckeCharacter/LevelModulus](../../ClassField/HeckeCharacter/LevelModulus.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Weil/Lift/Edge](Edge.md)
