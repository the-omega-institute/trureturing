# Low Rank Identity

## Abstract

Low Rank Identity

Orbit terms of theta kernel with standard ramified datum at parabolic points. Slice of the standard datum factors over the two summands. Equal-rank theta integral is constant; exchange identity at top of the tower.

**Theorem 1.1 (stdExchange_of_periods).**

Lean statement: `D5/S3/Zeros/GRH/New/Exchange/LowRankIdentity.stdExchange_of_periods`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Exchange/LowRankIdentity.stdExchange_of_periods` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

StdExchange holds for X, V′ ⊕ W₁, V′ and ℓ = |l|²/Π(rk W₁/2) if the splittings are adapted, rk W₁ is even, v, v′ are rapid, slices of v integrate over [U(W₁)] to ρ·l(𝔠) times those of v′ up to the Levi factor (ρ ≥ 0, non-zero near 1), and a support or sign condition holds.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Exchange/LowRankIdentity.stdExchange_of_periods`
- Dependency: [D5/S3/Zeros/GRH/Lib/SiegelWeil/Tower/LargeSideConstantTerm](../../Lib/SiegelWeil/Tower/LargeSideConstantTerm.md)
- Dependency: [D5/S3/Zeros/GRH/New/Exchange/NonnegativeVanishing](NonnegativeVanishing.md)
- Dependency: [D5/S3/Zeros/GRH/New/Exchange/StandardCoefficients](StandardCoefficients.md)
