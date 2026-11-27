# Twisted Hecke Type

## Abstract

Twisted Hecke Type

Valuation at N of character factors and of data given modulo N. Chain with denominators N equals scalar times chain mod N after Gauss-sum operator. Valuation of the restricted chain at the level prime N on a submodule. Scaled Hecke operator on algebraic forms has elementary divisors of small mean exponent.

**Theorem 1.1 (hasType_markOperator).**

Lean statement: `D5/S3/Zeros/GRH/New/Columns/TwistedHeckeType.hasType_markOperator`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Columns/TwistedHeckeType.hasType_markOperator` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let l lie in a marked set Λ, T be twisting data on the tops inducing l or l̄, and HeckeSizes hold. Then Y = Data.IsMarked.markOperator keeps the integral columns 𝒜, and [𝒜 : Y𝒜 + p^s𝒜] ∣ p^c, c ≤ (z + xs + y)·dim.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Columns/TwistedHeckeType.hasType_markOperator`
- Dependency: [D5/S3/Zeros/GRH/New/Seesaw/LiftCharacters](../Seesaw/LiftCharacters.md)
- Dependency: [D5/S3/Zeros/GRH/New/TwistedHecke/ElementaryDivisors](../TwistedHecke/ElementaryDivisors.md)
