---
bibkey: agrawal2004primes
authors: Manindra Agrawal; Neeraj Kayal; Nitin Saxena
year: 2004
title: "PRIMES is in P"
doi: 10.4007/annals.2004.160.781
claim: "Lemma 2.1 characterizes primality by (X+a)^n = X^n+a modulo n when gcd(a,n)=1. Theorem 4.1 proves the full AKS algorithm correct."
strata_touched: []
license: citation-only
triage: anchor
---

# Polynomial defects and the AKS coverage theorem

Primary source: *Annals of Mathematics* 160 (2004), 781–793.
Author manuscript: <https://www.cse.iitk.ac.in/users/manindra/algebra/primality_v6.pdf>.

Lemma 2.1 applies with `a=1` to the full polynomial
`(X+1)^n-X^n-1` in `(Z/nZ)[X]`. For a composite modulus, the proof
uses a prime divisor `q` and the coefficient of `X^q`, whose `q`-adic
valuation is smaller than that of `n`. Passing to a polynomial quotient
preserves the prime implication but can destroy its converse.

The algorithm in §4 checks perfect powers, chooses `r` with
`ord_r(n) > (log₂ n)^2`, checks small common divisors, and then checks
`1 ≤ a ≤ floor(sqrt(phi(r)) log₂ n)` modulo `X^r-1`.
Theorem 4.1 proves correctness; Lemma 4.3 bounds a suitable `r` by
`max(3, ceil((log₂ n)^5))`.

These are literature-attested results. They do not supply a coverage
theorem for replacing `X^r-1` with the k-bonacci polynomials while fixing
`a=1`. In particular, Lemma 4.5 uses the divisibility
`X^r-1 | X^(mr)-1`, a compatibility condition that must be re-established
for a different quotient family.

The k-bonacci application and exposure-depth definitions belong to
[the observer theory](../../docs/develop/theory/FORMAL_PRIME_OBSERVER_DYNAMICS.md),
§§302–308; this source does not assert those new applications.
