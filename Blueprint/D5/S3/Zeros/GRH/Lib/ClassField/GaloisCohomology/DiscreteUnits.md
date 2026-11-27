# Discrete Units

## Abstract

Discrete Units

Module over Z/l^r with small l-torsion admits primitive relation with prescribed zeros. Discrete modules with continuous action, restriction, exact sequences, functions on finite sets. Counting in exact sequences; left exactness of continuous 1-cocycles. Trivialised cocycles: extension from orbit representatives, corestriction, submultiplicative count in exact sequences. Additive notation for the multiplicative group of the algebraic closure.

**Theorem 1.1 (card_le_of_isShortExact).**

Lean statement: `D5/S3/Zeros/GRH/Lib/ClassField/GaloisCohomology/DiscreteUnits.card_le_of_isShortExact`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/ClassField/GaloisCohomology/DiscreteUnits.card_le_of_isShortExact` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

For 0 → A → B → C → 0 exact: if the trivialised cocycles DiscreteModule.trivialisedCocycles of A and C are finite in number, at most (#A)^k and (#C)^k, likewise for B; equality for B forces surjectivity onto those of C and equality for A.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/ClassField/GaloisCohomology/DiscreteUnits.card_le_of_isShortExact`
- Dependency: [D5/S3/Zeros/GRH/Lib/ClassField/Places/ProfiniteGalois](../Places/ProfiniteGalois.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/General/Groups/RatModInt](../../General/Groups/RatModInt.md)
