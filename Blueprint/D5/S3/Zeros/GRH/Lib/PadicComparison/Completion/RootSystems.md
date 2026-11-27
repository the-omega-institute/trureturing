# Root Systems

## Abstract

Root Systems

Derived completeness: Nakayama, retracts, cohomology, comparison mod a, completed base change. Tilting preserves products of two p-adic tests; product-preserving functors keep bijective pairs. Period pairs; period sheaf on p-adic tests is additive; p♭ kills coefficients modulo p. Functor of root systems with generator acting through roots of unity.

**Theorem 1.1 (pFlat_smul_eq_zero).**

Lean statement: `D5/S3/Zeros/GRH/Lib/PadicComparison/Completion/RootSystems.pFlat_smul_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/PadicComparison/Completion/RootSystems.pFlat_smul_eq_zero` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

If IsPeriodRingPair holds for (S, K), in particular p divides ξ in S, then π = ξ mod p annihilates O^♭ ⊗ S, the tensor product over A_inf.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/PadicComparison/Completion/RootSystems.pFlat_smul_eq_zero`
- Dependency: [D5/S3/Zeros/GRH/Lib/Cohomology/ProperBaseChange/ValuativeDensity](../../Cohomology/ProperBaseChange/ValuativeDensity.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/PadicHodge/PeriodRings/BdR](../../PadicHodge/PeriodRings/BdR.md)
