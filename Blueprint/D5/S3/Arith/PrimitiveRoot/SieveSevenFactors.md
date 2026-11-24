# Seven-prime supports in the threshold interval

## Abstract

Seven-prime supports in the threshold interval

**Theorem 1.1 (Ten exceptional seven-prime supports).**

Lean statement: `D5/S3/Arith/PrimitiveRoot/SieveSevenFactors.seven_shapes`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/SieveSevenFactors.seven_shapes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every sequence q of seven natural numbers, strict increase, primality of all entries and tail reciprocal mass above 73/137 hold if and only if the first five entries are 2, 3, 5, 7, 11 and the remaining pair is either (13,v), with v one of 17, 19, 23, 29, 31, 37, 41, 43, or (17,19) or (17,23). Ordered prime ranks and six rational comparisons exclude all other branches; the ten listed tails each have the required strict reciprocal mass. The conclusion thus classifies the excessive-mass supports in both directions, including their ordering and primality.

**Theorem 1.2 (Eight integers from exceptional radicals).**

Lean statement: `D5/S3/Arith/PrimitiveRoot/SieveSevenFactors.seven_candidates`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/SieveSevenFactors.seven_candidates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A natural number x is in the eight-element set below if and only if 3483482 ≤ x < 4144141, x-1 has seven distinct prime factors and their tail has reciprocal sum greater than 73/137. The set is {3573571, 4084081, 3993991, 3723721, 3693691, 3873871, 3730651, 3612841}. The product of the distinct factors divides x-1. Consequently the classification covers every multiple of the ten radicals, including integers for which x-1 is not squarefree. This theorem lists the remaining arithmetic candidates. Conversely, their sorted supports and strict reciprocal inequalities hold. No sieve feasibility or primality is asserted.

## References

- Truth anchor: `D5/S3/Arith/PrimitiveRoot/SieveSevenFactors.seven_candidates`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/SieveSevenFactors.seven_shapes`
- Dependency: [D5/S3/Arith/PrimitiveRoot/SievePrimeFactors](SievePrimeFactors.md)
