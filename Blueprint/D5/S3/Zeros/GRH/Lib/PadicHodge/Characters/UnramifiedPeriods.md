# Unramified Periods

## Abstract

Unramified Periods

Algebra lemma: killing polynomials in all positive degrees give one in degree zero. Finite type, weights, killing polynomials pass to retracts and along open embeddings. Twisting by a character keeps goodness, shifts weights, rescales killing polynomials. Potentially unramified characters are potentially crystalline, with jumps and Frobenius; Lang for GL_1.

**Theorem 1.1 (isPotCrys_of_unramified_char).**

Lean statement: `D5/S3/Zeros/GRH/Lib/PadicHodge/Characters/UnramifiedPeriods.isPotCrys_of_unramified_char`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/PadicHodge/Characters/UnramifiedPeriods.isPotCrys_of_unramified_char` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let j be an open embedding, ν: Γ → Q̄_p^× a continuous character trivial on inertia near 1, acting by scalars on a commutative Q̄_p-algebra T. Then T is potentially crystalline, has the jumps of the trivial action, and X − ν(s) kills (s, k) for Weil pairs (j(s), k).

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/PadicHodge/Characters/UnramifiedPeriods.isPotCrys_of_unramified_char`
- Dependency: [D5/S3/Zeros/GRH/Lib/GaloisRep/Pseudocharacter/FibreSum](../../GaloisRep/Pseudocharacter/FibreSum.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/PadicHodge/Crystalline/GoodCriterion](../Crystalline/GoodCriterion.md)
