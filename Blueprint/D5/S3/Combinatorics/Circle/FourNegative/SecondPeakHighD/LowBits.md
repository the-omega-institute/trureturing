# Low bits of a dyadic predecessor

## Abstract

Low bits of a dyadic predecessor

**Theorem 1.1 (bit below).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits.bit_below`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits.bit_below` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed part of low bits of a dyadic predecessor. The complete module scope and assumptions are stated below.

**Theorem 1.2 (submask of land).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits.submask_of_land`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits.submask_of_land` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed part of low bits of a dyadic predecessor. The complete module scope and assumptions are stated below.

**Theorem 1.3 (submask predecessor).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits.submask_predecessor`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits.submask_predecessor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed part of low bits of a dyadic predecessor. The complete module scope and assumptions are stated below.

Submask m M means every true testBit of m is true in M. A bit of m<2^k lies below k. The existing private multiple_predecessor_bits lemma proves that every position below k is true in 2^k*n-1 for n>=1. These two statements supply submask_predecessor; small_proper_predecessor additionally obtains strict m<M when n>=2.

The land equality m &&& M=m gives the same bit inclusion and is used only for the twenty genuinely finite h=4 rows. No finite test is used to infer an unbounded dyadic family.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits.bit_below`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits.submask_of_land`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits.submask_predecessor`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/Algebra](Algebra.md)
