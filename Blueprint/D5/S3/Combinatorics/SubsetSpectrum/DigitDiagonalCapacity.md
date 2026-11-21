# Counting integer levels along digit diagonals

## Abstract

A bound on integer masses represented by two bounded digits.

**Theorem 1.1 (The integer-level count is bounded by the diagonal code count).**

$$\forall k n b c a z, 0 < b \land \operatorname{Coprime}\left(c, b\right) \land a+z=\frac{c}{b} \land \operatorname{Coverage}\left(k, n, a, z\right) \Rightarrow n\le \operatorname{DiagonalCodeCount}\left(k, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubsetSpectrum/DigitDiagonalCapacity.integral_range_le_diagonal_codes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k and n be natural numbers. Suppose two real weights a and z sum to c divided by b, where c and b are coprime natural numbers and b is positive. Coverage(k,n,a,z) means each integer level from zero through n minus one is a weighted sum of two digits between zero and k. DiagonalCodeCount(k,b) is the number of distinct triples obtained from all such digit pairs. The first two entries are the two truncated differences of the digits. The third entry is their minimum divided by b, rounded down.

The first two entries determine the diagonal. Two representations of integers on the same diagonal differ in mass by c divided by b times the change of position. Coprimality forces those positions to agree modulo b. Matching quotients then give the same position and the same represented integer. Choosing one representation per covered integer injects the interval into the finite set of codes.

A diagonal of length L contributes the ceiling of L divided by b codes. For k equal to eight and b equal to four, the central diagonal contributes three and the remaining diagonals contribute twenty-four.

## References

- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/DigitDiagonalCapacity.integral_range_le_diagonal_codes`
