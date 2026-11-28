# Crystalline Rank

## Abstract

Crystalline Rank

the rank of the crystalline cocycles Z_f(L) is rk L plus the number of negative Hodge–Tate weights; so a power of ℓ that maps Z_f(L) into a submodule bounds the quotient in length.

**Theorem 1.1 (normLength_defect_le).**

Lean statement: `D5/S3/Zeros/GRH/New/Selmer/CrystallineRank.normLength_defect_le`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Selmer/CrystallineRank.normLength_defect_le` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let L be potentially crystalline, ℓ^k Z_f(L) ⊆ S for a submodule S, and 2k·rank L ≤ y. Then Z_f(L) modulo Z_f(L) ∩ S has normalised length at most y times the index of j(Γ) in the absolute Galois group of ℚ_ℓ.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Selmer/CrystallineRank.normLength_defect_le`
- Dependency: [D5/S3/Zeros/GRH/Lib/ClassField/LocalDuality/CrystallineDuality](../../Lib/ClassField/LocalDuality/CrystallineDuality.md)
- Dependency: [D5/S3/Zeros/GRH/New/Selmer/ThickSpacing](ThickSpacing.md)
