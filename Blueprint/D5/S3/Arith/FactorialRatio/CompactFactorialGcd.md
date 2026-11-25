# The compact factorial gcd

## Abstract

A two-sided divisibility bound for the gcd of a one-parameter factorial family.

An Alpoge-inspired rank-one window calculation motivates the comparison. The proof uses a GPT Pro derivation and an independent derivation of the integer bound with budget (2r^2)!.

**Definition 1.1 (Factorial product).**

Lean statement: `D5/S3/Arith/FactorialRatio/CompactFactorialGcd.selbergFactorial`

*Formalization.* `D5/S3/Arith/FactorialRatio/CompactFactorialGcd.selbergFactorial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural r, s and b with rb at most s, take the product over j=1,...,r of (jb)! divided by b!, times (s-(r-j)b)!. Each division by b! is exact.

**Definition 1.2 (Gcd of the factorial products).**

Lean statement: `D5/S3/Arith/FactorialRatio/CompactFactorialGcd.selbergGcd`

*Formalization.* `D5/S3/Arith/FactorialRatio/CompactFactorialGcd.selbergGcd` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The gcd of the factorial products over 0<=b<=floor(s/r). The parameter zero supplies the product (s!)^r.

**Theorem 1.3 (Exact two-sided divisibility).**

Lean statement: `D5/S3/Arith/FactorialRatio/CompactFactorialGcd.compact_factorial_gcd`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/CompactFactorialGcd.compact_factorial_gcd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of natural numbers r and s with r>=2 and s<r^2, tailLCM(rs+r-1,r-1) divides selbergGcd(r,s), and selbergGcd(r,s) divides tailLCM(rs+r-1,r-1) times (2r^2)!. The tail product multiplies the prefix LCM at floor((rs+r-1)/k) over r-1<k<=rs+r-1.

At each prime power, a count of marked residues in consecutive blocks bounds the paired factorial floors below by the corresponding tail count. Summing via Legendre's formula proves the lower divisibility for every b. For a prime p<=r the parameter b=0 bounds the excess by (r-1) times the number of positive powers of p at most s. For r<p<=s the parameter b=floor(p/r) bounds the excess using only the first power of p. In both cases the bound is at most floor(2r^2/p). Primes above s contribute zero to the gcd.

At s=0 both the tail and gcd equal one. When r=3 and s=8, the tail product is 41803776000 and the gcd is 83607552000, so the quotient equals two.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/CompactFactorialGcd.compact_factorial_gcd`
- Truth anchor: `D5/S3/Arith/FactorialRatio/CompactFactorialGcd.selbergFactorial`
- Truth anchor: `D5/S3/Arith/FactorialRatio/CompactFactorialGcd.selbergGcd`
- Dependency: [D5/S3/Arith/FactorialRatio/RankOneLCMGcd](RankOneLCMGcd.md)
