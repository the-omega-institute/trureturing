# Primitive Periods

## Abstract

Primitive Periods

Primitive comparison modulo p lifts to period-ring coefficients.

**Theorem 1.1 (exists_primitive_period_comparison).**

Lean statement: `D5/S3/Zeros/GRH/Lib/PadicComparison/Primitive/PrimitivePeriods.exists_primitive_period_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/PadicComparison/Primitive/PrimitivePeriods.exists_primitive_period_comparison` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Primitive comparison: let (S, K) satisfy IsPeriodRingPair, K flat over S, Ψ ≅ K ⊗ (S ⊗ W(c^♭))^ on p-adic tests c. The natural map K ⊗ W(LC(Spec c[1/p], 𝔽_p)) → Ψ is bijective on cohomology along α: N' → N if N, N' have flat base change, all Hⁿ(N, ℤ_p) are finitely generated, and primitiveMap ⊗ (S/p) ⊗ 𝔪 is.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/PadicComparison/Primitive/PrimitivePeriods.exists_primitive_period_comparison`
- Dependency: [D5/S3/Zeros/GRH/Lib/Cohomology/Etale/EllAdicCohomology](../../Cohomology/Etale/EllAdicCohomology.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/PadicComparison/Primitive/TiltedTheory](TiltedTheory.md)
