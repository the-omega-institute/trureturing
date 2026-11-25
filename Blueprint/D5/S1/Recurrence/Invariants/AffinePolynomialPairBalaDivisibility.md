# Bala's terminating identity and divisibility for h_d

## Abstract

The binomial column family h_d satisfies Bala's terminating identity, and for moduli coprime to (d − 1)! the divisors of h_d(m) are exactly those of its product formula.

**Theorem 1.1 (Terminating identity and divisibility).**

Lean statement: `D5/S1/Recurrence/Invariants/AffinePolynomialPairBalaDivisibility.result`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/AffinePolynomialPairBalaDivisibility.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Extensions of Knuth's coefficient families (1993), with corrected OEIS links: Werner's conjecture in OEIS A208509, Formula, revision 28*. DOI: [10.5281/zenodo.24211281](https://doi.org/10.5281/zenodo.24211281). URL: <https://zenodo.org/records/24211281>.

*Commentary.*

Here h_d(m) = [z^m](1 + z)/(1 − z)^d. For every d ≥ 0 and n ≥ 1, the sum over 0 ≤ j ≤ n of (−1)^j h_d(j) · n(n − 1)⋯(n − j + 1) / ((n + d)(n + d + 1)⋯(n + d + j − 1)) vanishes, empty products being 1. For d ≥ 2 and q coprime to (d − 1)!, q divides h_d(m) exactly when q divides (2m + d − 1)(m + 1)(m + 2)⋯(m + d − 2). Hence q divides h_d(m) when q divides m + j for some 1 ≤ j ≤ d − 2, or q divides 2m + d − 1; in particular this holds for q = p^e with p > d − 1 prime and every e ≥ 0. The converse of this sufficient condition fails: h_3(2) = 9, while 9 divides neither m + 1 = 3 nor 2m + d − 1 = 6.

Multiplying the j-th term by (2n + d − 1)!/(n!(n + d − 1)!) turns it into (−1)^j h_d(j) C(2n + d − 1, n − j). The alternating series of h_d is (1 − z)/(1 + z)^d, so these integers are the coefficients of z^n in (1 − z)(1 + z)^{2n − 1}, namely C(2n − 1, n) − C(2n − 1, n − 1) = 0. For divisibility, (d − 1)! h_d(m) = (2m + d − 1)(m + 1)(m + 2)⋯(m + d − 2), and q is coprime to (d − 1)!, so it can be cancelled.

The hypotheses are needed. At n = 0 the sum is h_d(0) = 1. For d = 1, m = 2 and q = 4, q divides 2m + d − 1 = 4 and is coprime to 0! = 1, but h_1(2) = 2. For d = 4, m = 1 and q = 2, q divides m + 1 but h_4(1) = 5; here q is not coprime to 3! = 6. The source states the identity for d ≥ 2 and the divisibility for prime powers with e ≥ 1; it is Corollary 7 of H. Ma and W. Zhang's note on A208509 (DOI 10.5281/zenodo.24211281), which credits the identity to Bala (2019) and notes that the prime-power case for d = 6 contains Adamchuk's 2007 divisibility assertions in A005585.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/AffinePolynomialPairBalaDivisibility.result`
- Dependency: [D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialColumnFamily](AffinePolynomialPairBinomialColumnFamily.md)
