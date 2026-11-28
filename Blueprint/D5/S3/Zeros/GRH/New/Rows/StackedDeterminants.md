# Stacked Determinants

## Abstract

Stacked Determinants

Record of auxiliary dual pair: levels, characters, data, theta descent, Hecke test polynomial. Record of the splitting of V, residue rings modulo squared level, generator idele. Bordered determinant, trivial modulus, the carrier lift and the summing form. Products of bordered determinants, their substitution law, and coordinates in a Schur basis.

**Theorem 1.1 (twoSidedSubst_stackedDetProd).**

Lean statement: `D5/S3/Zeros/GRH/New/Rows/StackedDeterminants.twoSidedSubst_stackedDetProd`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Rows/StackedDeterminants.twoSidedSubst_stackedDetProd` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

The substitution x_τ ↦ c_τᵀ x_τ g_τᵀ sends the product over τ, k of the determinants of M_{τk} g_τᵀ stacked over x_τ to ∏_τ (det c_τ · det g_τ)^{#ι(τ)} times the same product for the matrices M_{τk}.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Rows/StackedDeterminants.twoSidedSubst_stackedDetProd`
- Dependency: [D5/S3/Zeros/GRH/Lib/ClassField/HeckeCharacter/LevelModulus](../../Lib/ClassField/HeckeCharacter/LevelModulus.md)
- Dependency: [D5/S3/Zeros/GRH/New/Rows/PartnerCut](PartnerCut.md)
- Dependency: [D5/S3/Zeros/GRH/New/Rows/SemiInvariantNorm](SemiInvariantNorm.md)
