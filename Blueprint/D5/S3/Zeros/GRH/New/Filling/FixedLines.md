# Fixed Lines

## Abstract

Fixed Lines

A group Z between K(g) and K for which Level.floorZeroForm Z, divided by the measure of Z, is smaller than for K by b^(6|κ|) for each given place above q₀ where a frame vector is fixed.

**Theorem 1.1 (exists_intermediateGroup_lines).**

Lean statement: `D5/S3/Zeros/GRH/New/Filling/FixedLines.exists_intermediateGroup_lines`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Filling/FixedLines.exists_intermediateGroup_lines` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let Sg be a set of chosen places above q₀, and 1/g integral off T. Some group K(g) ≤ Z ≤ K contains k_T whenever k reduces into Filling.fixingSet Sg d, and kk(Z)·M(K)·b^(6|κ||Sg|) ≤ kk(K)·M(Z), kk = Level.floorZeroForm, M = Level.groupMeasure.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Filling/FixedLines.exists_intermediateGroup_lines`
- Dependency: [D5/S3/Zeros/GRH/New/Filling/GlobalToLocal](GlobalToLocal.md)
