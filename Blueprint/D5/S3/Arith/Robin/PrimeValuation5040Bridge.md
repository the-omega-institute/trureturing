# The 5040 Prime-Valuation Fibre

## Abstract

The 5040 block is the exact simultaneous valuation fibre at the four active primes.

This finite arithmetic bridge extracts the canonical prime-power block from a nonzero natural number. The residual factor is coprime to the external unit modulus and to 210=2*3*5*7, so the four valuations are exactly the profile (4,2,1,1). The proof uses the repository's finite prime-power product and the existing 5040 support; it makes no analytic claim about RH.

**Theorem 1.1 (Exact residual characterization of the 5040 fibre).**

Lean statement: `D5/S3/Arith/Robin/PrimeValuation5040Bridge.jointFiber5040_mul_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PrimeValuation5040Bridge.jointFiber5040_mul_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every external modulus W coprime to 2,3,5,7 and every natural n, the simultaneous factorization fibre of 5040*n is equivalent to n being nonzero and coprime to W*210.

The forward direction extracts nonzeroness and the four zero residual valuations. The reverse direction uses multiplicativity of natural factorization, the imported prime-power product, and coprimality to the active support. This is the finite bridge consumed by Robin records; analytic inequalities and the RH implication remain outside this declaration.

**Lemma 1.2 (The profile is the factorization of 5040).**

Lean statement: `D5/S3/Arith/Robin/PrimeValuation5040Bridge.profile5040_eq_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PrimeValuation5040Bridge.profile5040_eq_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The imported target exponent profile agrees pointwise with the natural factorization of 5040, giving exponents 4,2,1,1 on 2,3,5,7 and zero elsewhere.

## References

- Truth anchor: `D5/S3/Arith/Robin/PrimeValuation5040Bridge.jointFiber5040_mul_iff`
- Truth anchor: `D5/S3/Arith/Robin/PrimeValuation5040Bridge.profile5040_eq_factorization`
- Dependency: [D5/S3/Arith/GoldenResource/GoldenDivisorLanguage](../GoldenResource/GoldenDivisorLanguage.md)
- Dependency: [D5/S3/Arith/GoldenResource5040PriceInterval](../GoldenResource5040PriceInterval.md)
- Dependency: [D5/S3/Factorization/PrimePowers/FiniteCrtJoin](../../Factorization/PrimePowers/FiniteCrtJoin.md)
