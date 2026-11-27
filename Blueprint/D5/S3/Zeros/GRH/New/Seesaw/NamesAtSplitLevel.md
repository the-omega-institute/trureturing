# Names At Split Level

## Abstract

Names At Split Level

Abstract lift laws mod N; Gauss-sum Hecke operator slides through a chain of lifts. Jointly invariant chain of lifts is a plain sum over tuples of classes. Translates with denominator N on a pair rewritten as named data modulo N.

**Theorem 1.1 (translateSum_eq_sum_name).**

Lean statement: `D5/S3/Zeros/GRH/New/Seesaw/NamesAtSplitLevel.translateSum_eq_sum_name`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Seesaw/NamesAtSplitLevel.translateSum_eq_sum_name` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let P, S satisfy IsSplitLevel for N with P ∪ P̄ = S ∪ S̄, and u, u' be the projections Space.projOn S of v, v'. Then τ_N(u ⊗ u') at S is ∑_z (𝐛_z(·D) ⊗ v) ⊗ (𝐜_z(D'·) ⊗ v'), names at P, with D, D' = diag(1, …, 1, N) on P ∩ S, P ∖ S.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Seesaw/NamesAtSplitLevel.translateSum_eq_sum_name`
- Dependency: [D5/S3/Zeros/GRH/Lib/Weil/Lift/Staircase](../../Lib/Weil/Lift/Staircase.md)
