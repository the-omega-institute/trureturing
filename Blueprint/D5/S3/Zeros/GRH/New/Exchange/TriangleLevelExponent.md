# Triangle Level Exponent

## Abstract

Triangle Level Exponent

Integrality of the lift; integral group-ring element interpolating tame twists of L-values. Normalised squared norm of a character's theta lift is constant times Hecke L-value. Exchange constant for a twist rewritten through L-value ratios and conductor norms. Spaces and characters of the triangle of lifts.

**Theorem 1.1 (lValueProd_eq).**

Lean statement: `D5/S3/Zeros/GRH/New/Exchange/TriangleLevelExponent.lValueProd_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Exchange/TriangleLevelExponent.lValueProd_eq` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let Π be lValueProd, (ν, z) a pair, ϑ tame of modulus Q, s = ±1. Then Π(z) for (νϑ^s)⁻¹ away from the chosen places and Q is N(Q)^{z²} times Π(z) for ν⁻¹ away from the chosen places times ∏_{1≤z'≤z} ρ_{z'}², ρ_{z'} the L-value ratio Data.Pair.ratio.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Exchange/TriangleLevelExponent.lValueProd_eq`
- Dependency: [D5/S3/Zeros/GRH/New/Exchange/CharacterLiftNorm](CharacterLiftNorm.md)
- Dependency: [D5/S3/Zeros/GRH/New/Exchange/ExchangeTheorem](ExchangeTheorem.md)
- Dependency: [D5/S3/Zeros/GRH/New/Rows/LineArithmetic](../Rows/LineArithmetic.md)
- Dependency: [D5/S3/Zeros/GRH/New/Seesaw/PairTensorData](../Seesaw/PairTensorData.md)
