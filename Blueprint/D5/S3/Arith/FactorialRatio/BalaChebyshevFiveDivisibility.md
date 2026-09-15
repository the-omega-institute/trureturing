# Chebyshev Factorial Ratio Divisibility by 5n+1

## Abstract

The Chebyshev factorial ratio is divisible by 5n+1 at every natural index.

**Theorem 1.1 (Local five-modulus floor defect).**

Lean statement: `D5/S3/Arith/FactorialRatio/BalaChebyshevFiveDivisibility.local_five`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/BalaChebyshevFiveDivisibility.local_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive modulus q, the floor defect is nonnegative; for q at least six dividing 5n+1, it equals one.

**Theorem 1.2 (Top-scale unit defect).**

Lean statement: `D5/S3/Arith/FactorialRatio/BalaChebyshevFiveDivisibility.top_scale_unit`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/BalaChebyshevFiveDivisibility.top_scale_unit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive n and 10n < q <= 30n, the floor defect equals one.

**Theorem 1.3 (Bala's 5n+1 integrality clause).**

Lean statement: `D5/S3/Arith/FactorialRatio/BalaChebyshevFiveDivisibility.bala_five_integrality`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/BalaChebyshevFiveDivisibility.bala_five_integrality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, including zero, (5n+1)(15n)!(10n)!(6n)! divides (30n)!n!. This is the 5n+1 clause of Peter Bala's August 2025 integrality conjectures for OEIS A211417, distinct from the previously proved 3n+1 and 30n-1 clauses.

The known 3n+1 theorem supplies base factorial-ratio integrality. For prime powers q at least six dividing 5n+1, the floor defect is exactly one. The prime five does not divide 5n+1. At two, the factorial valuation equals that of the binomial coefficient 8n choose 5n, and the adjacent-binomial identity supplies the extra factor. At three, the potentially missing contribution from q=3 is supplied at a different scale: the first power of three strictly above 10n is at most 30n and has floor defect one. It is larger than 5n+1, so this contribution does not duplicate any of the divisibility exponents.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/BalaChebyshevFiveDivisibility.bala_five_integrality`
- Truth anchor: `D5/S3/Arith/FactorialRatio/BalaChebyshevFiveDivisibility.local_five`
- Truth anchor: `D5/S3/Arith/FactorialRatio/BalaChebyshevFiveDivisibility.top_scale_unit`
- Dependency: [D5/S3/Arith/FactorialRatio/BalaChebyshevThreeDivisibility](BalaChebyshevThreeDivisibility.md)
