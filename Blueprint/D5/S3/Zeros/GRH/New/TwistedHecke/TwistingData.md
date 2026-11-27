# Twisting Data

## Abstract

Twisting Data

Frobenius-twisted circle of letters: action, depth, excess, weight conditions, basic properties.

**Theorem 1.1 (polyAction_polyOfCoeffs).**

Lean statement: `D5/S3/Zeros/GRH/New/TwistedHecke/TwistingData.polyAction_polyOfCoeffs`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/TwistedHecke/TwistingData.polyAction_polyOfCoeffs` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

For a coefficient vector F, g sends ∑_β F(β) x^β to ∑_β (ρ(g)F)(β) x^β: the matrix ρ(g) = TwistingData.letterRep n g represents the action on forms of degree n in each letter.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/TwistedHecke/TwistingData.polyAction_polyOfCoeffs`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/Algebra/ZerosCostDegree](../../Lib/General/Algebra/ZerosCostDegree.md)
