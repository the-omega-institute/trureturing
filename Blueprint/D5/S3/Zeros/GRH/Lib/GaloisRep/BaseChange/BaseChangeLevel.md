# Base Change Level

## Abstract

Base Change Level

Tame levels; matching of unit functions at principal congruence level, keeping unramified places maximal.

**Theorem 1.1 (exists_baseChange_level).**

Lean statement: `D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/BaseChangeLevel.exists_baseChange_level`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/BaseChangeLevel.exists_baseChange_level` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

For a step, σ ≠ 1 and H open: there are levels K_u ≤ GL_n(O_u) over E', maximal above IsStepUnramifiedAt places w with K_w ≤ H, pulling back into H; each level L above S is open, σ-stable, satisfies CocyclesSplit, and its indicators form a IsMatchingPairAbove.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/BaseChangeLevel.exists_baseChange_level`
- Dependency: [D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/BaseChangeWeight](BaseChangeWeight.md)
