# Tame Inertia

## Abstract

Tame Inertia

Structure of tame inertia: acts through roots of uniformiser, Frobenius acts by q.

**Theorem 1.1 (tame_inertia).**

Lean statement: `D5/S3/Zeros/GRH/Lib/ClassField/Places/TameInertia.tame_inertia`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/ClassField/Places/TameInertia.tame_inertia` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let n be a unit of A, yⁿ a uniformiser of k, f on inertia with open kernel and fⁿ = 1. Then f kills the stabiliser of y, f(s) generates the image if sy/y has order n, and f(φsφ⁻¹) = f(s)^q for a q-Frobenius φ.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/ClassField/Places/TameInertia.tame_inertia`
- Dependency: [D5/S3/Zeros/GRH/Lib/ClassField/GaloisCohomology/SylowReduction](../GaloisCohomology/SylowReduction.md)
