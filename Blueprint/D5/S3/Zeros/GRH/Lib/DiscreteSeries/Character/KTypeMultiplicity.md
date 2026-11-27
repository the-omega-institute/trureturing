# K Type Multiplicity

## Abstract

K Type Multiplicity

Weyl character and denominator formulas for U(p)×U(q); conjugacy into the torus. K-type multiplicities of discrete series: integer, one at lowest type, supported in cone.

**Theorem 1.1 (exists_kType_multiplicity).**

Lean statement: `D5/S3/Zeros/GRH/Lib/DiscreteSeries/Character/KTypeMultiplicity.exists_kType_multiplicity`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/DiscreteSeries/Character/KTypeMultiplicity.exists_kType_multiplicity` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Multiplicity of a K-type. Let l = 2λ have gap 500n³+A, n ≥ 1, ν be K-dominant. Then g ↦ ∫_K χ̄_ν(k)ψ_λ(g⁻¹kg)dk is integrable, and deg_λ times its integral is some m∈ℕ; m = 1 for ν = Λ = HCParam.lowestKType l, and m ≠ 0 forces ν−Λ∈HCParam.rootCone l.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/DiscreteSeries/Character/KTypeMultiplicity.exists_kType_multiplicity`
- Dependency: [D5/S3/Zeros/GRH/Lib/DiscreteSeries/Character/LaurentAlternants](LaurentAlternants.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/GLn/SchurModule/SchurOrthogonality](../../GLn/SchurModule/SchurOrthogonality.md)
