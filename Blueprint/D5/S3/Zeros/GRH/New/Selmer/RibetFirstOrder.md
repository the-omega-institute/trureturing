# Ribet First Order

## Abstract

Ribet First Order

Fitting ideal of one character contains ∏X_j times a polynomial with bounded constant term. Abstract first-order Ribet lemma with congruent blocks, ties and Fitting ideal bound.

**Theorem 1.1 (ribet_first_order).**

Lean statement: `D5/S3/Zeros/GRH/New/Selmer/RibetFirstOrder.ribet_first_order`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Selmer/RibetFirstOrder.ribet_first_order` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Ribet's lemma to first order: on 𝓧, u_x is a block plus characters ξ_e, ξ_0 = 1; β_x is the determinant of the combination ribetNormaliser of the u_x(g) − 1. Some f in S has fβ ∈ 𝒥; on 𝓧, β = 0 and f has no term properly dividing ∏X_j; that coefficient at π has valuation ≤ b₀ + Σ b_e + explicit losses.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Selmer/RibetFirstOrder.ribet_first_order`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/Algebra/BlockFittingBound](../../Lib/General/Algebra/BlockFittingBound.md)
- Dependency: [D5/S3/Zeros/GRH/New/Selmer/BlocksAndCocycles](BlocksAndCocycles.md)
- Dependency: [D5/S3/Zeros/GRH/New/Selmer/RibetCramer](RibetCramer.md)
