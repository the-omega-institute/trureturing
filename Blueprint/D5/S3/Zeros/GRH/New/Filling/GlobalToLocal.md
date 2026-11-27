# Global To Local

## Abstract

Global To Local

Dictionary between global data and the places in T; phase sums as local integrals.

**Theorem 1.1 (correlation_smul_eq_cosetAmplitude).**

Lean statement: `D5/S3/Zeros/GRH/New/Filling/GlobalToLocal.correlation_smul_eq_cosetAmplitude`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Filling/GlobalToLocal.correlation_smul_eq_cosetAmplitude` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Unfolding: let σ fix all e_a, e*_a, γ = w_pσ, h_c⁻¹γh_c' and 1/g be integral off T, k ∈ K, k_T⁻¹ab⁻¹ ∈ K(g). Then entry (a,b) of Level.correlation at (h_c⁻¹σh_c')_T⁻¹, times the archimedean besselCorrelation at γ, equals κ_ϱ(p,1)·M(K(g))·Filling.cosetAmplitude over (c, k̄, c'), cut off at T.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Filling/GlobalToLocal.correlation_smul_eq_cosetAmplitude`
- Dependency: [D5/S3/Zeros/GRH/New/Filling/AmplitudeSums](AmplitudeSums.md)
- Dependency: [D5/S3/Zeros/GRH/New/Filling/GlobalSieve](GlobalSieve.md)
- Dependency: [D5/S3/Zeros/GRH/New/Filling/TopFloor](TopFloor.md)
