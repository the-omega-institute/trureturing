# One Vector

## Abstract

One Vector

Siegel's mean value formula for representing one number by a sum of norms.

**Theorem 1.1 (classSum_norm_eq).**

Lean statement: `D5/S3/Zeros/GRH/Lib/SiegelWeil/OneVector/OneVector.classSum_norm_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/SiegelWeil/OneVector/OneVector.classSum_norm_eq` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Siegel's formula. Let n = |κ| ≥ 3, K ⊂ K₀ open, Φ₀ ≥ 0 K-invariant Schwartz–Bruhat, α = ᾱ totally positive. Then ∑_{x∈E^n, x*x=α} Φ₀(h⁻¹x) converges, and its K-class sum is (class sum of 1)·|D_E|^{1/4}·∏_v π^n α_v^{n−1}/(n−1)!·∫∫Φ₀(x)ψ_f(z(x*x−α)/2) dx dz, z = z̄ a finite adele, measures volÔ, volume_codifferent.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/SiegelWeil/OneVector/OneVector.classSum_norm_eq`
- Dependency: [D5/S3/Zeros/GRH/Lib/Analytic/Landau/PolarLandau](../../Analytic/Landau/PolarLandau.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/SiegelWeil/Formula/SiegelWeilFormula](../Formula/SiegelWeilFormula.md)
