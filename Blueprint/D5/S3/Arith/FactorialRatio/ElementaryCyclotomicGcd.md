# Cyclotomic carry products

## Abstract

An exact prime-power carry factorization of a product of prefix least common multiples.

**Definition 1.1 (Carry product for one row).**

Lean statement: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicGcd.QStar`

*Formalization.* `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicGcd.QStar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply p once for each positive prime power r = p^t up to 4(N-j)+1 for which the integer quotient floor(4j/r) is odd.

**Definition 1.2 (Accumulated carry product).**

Lean statement: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicGcd.HStar`

*Formalization.* `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicGcd.HStar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply the individual carry products over j from zero through N.

**Definition 1.3 (Exceptional factor).**

Lean statement: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicGcd.EStar`

*Formalization.* `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicGcd.EStar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The level two contributes 2^N. For each odd prime power r = p^t up to 4N+1, count the nonnegative indices j below N+1-floor((r+2)/4) where r divides j when r is 1 modulo 4, or r divides 4j+1 when r is 3 modulo 4. Each such index contributes a factor p.

**Theorem 1.4 (Exact accumulated LCM identity).**

Lean statement: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicGcd.lcmProduct_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicGcd.lcmProduct_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product of the prefix least common multiples through 4i+1 for i from zero through N equals the product of the central binomial coefficients binom(4i,2i) times the accumulated carry product and the exceptional factor.

At level r, shift the binomial index by floor((r+2)/4) to match the range of the truncated carry. The two carries add to one at each odd level outside its exceptional residues and to zero on those residues. The sum is always one at powers of two from four onward. At level two the carries vanish and the prefix least common multiples contribute N occurrences.

**Theorem 1.5 (Divisibility bound for the exceptional factor).**

Lean statement: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicGcd.EStar_dvd`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicGcd.EStar_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exceptional factor divides 2^N times the least common multiple through 4N+1 times the product of j(4j+1) over j from one through N. The index zero contributes at most one copy of each prime-power level in the least common multiple. Each positive index contributes only levels dividing j or 4j+1.

**Theorem 1.6 (Explicit sampled Chebyshev comparison).**

Lean statement: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicGcd.log_HStar_sub_sampled_chebyshev_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicGcd.log_HStar_sub_sampled_chebyshev_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The absolute difference between log HStar and the sum of psi(4i+1) over i from zero through N, after subtracting 2 log(2) N(N+1) from the sum, is at most 14 N log(N+2). Take logarithms of the exact identity using the prefix LCM formula for psi. Bounds on the central binomial coefficients and on the divisibility budget bound the two errors.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicGcd.EStar`
- Truth anchor: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicGcd.EStar_dvd`
- Truth anchor: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicGcd.HStar`
- Truth anchor: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicGcd.QStar`
- Truth anchor: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicGcd.lcmProduct_eq`
- Truth anchor: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicGcd.log_HStar_sub_sampled_chebyshev_le`
- Dependency: [D5/S3/Arith/FactorialRatio/CompactFactorialGcd](CompactFactorialGcd.md)
