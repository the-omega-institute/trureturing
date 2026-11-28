# Elementary Divisors

## Abstract

Elementary Divisors

Twisted Hecke operator has small elementary divisors; approximate projector; Smith form of ends.

**Theorem 1.1 (A capped full minor from the pairing).**

Lean statement: `D5/S3/Zeros/GRH/New/TwistedHecke/ElementaryDivisors.of_pairing_capped_minor`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/TwistedHecke/ElementaryDivisors.of_pairing_capped_minor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The residue-space dimension bounds the number of retained Smith indices. The corresponding correction factors through those indices, so the block determinant construction gives a nonzero full column minor of the capped pairing matrix. Its determinant divides the scalar pairing budget.

**Theorem 1.2 (hasType_twisted_hecke).**

Lean statement: `D5/S3/Zeros/GRH/New/TwistedHecke/ElementaryDivisors.hasType_twisted_hecke`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/TwistedHecke/ElementaryDivisors.hasType_twisted_hecke` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Elementary divisors of the twisted Hecke operator (AF)(c) = ∑_b (u_e ⊗ (ρ(g_e) p^{depth} ρ(γ_b))ᵀ) F(src e), e = (c,b), the γ_b representing the cosets 𝒫γ of the parahoric. Assume p is a non-unit, HeckeSizes, and e ↦ (src e, 𝒫g_eᵀ) injective. If Yf = fA, then Y has type (z + κm + y)|X||I| at m on im f (HasType: Y preserves M = im f, and YM + p^m M has index dividing p^l for some l at most this number).

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/TwistedHecke/ElementaryDivisors.hasType_twisted_hecke`
- Truth anchor: `D5/S3/Zeros/GRH/New/TwistedHecke/ElementaryDivisors.of_pairing_capped_minor`
- Dependency: [D5/S3/Zeros/GRH/New/Core/CappedMinorWitness](../Core/CappedMinorWitness.md)
- Dependency: [D5/S3/Zeros/GRH/New/Core/ModuleIndex](../Core/ModuleIndex.md)
- Dependency: [D5/S3/Zeros/GRH/New/TwistedHecke/Counting](Counting.md)
