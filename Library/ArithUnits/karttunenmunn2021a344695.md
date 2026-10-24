---
bibkey: karttunenmunn2021a344695
authors: Antti Karttunen; Peter Munn
year: 2021
title: "OEIS A344695: gcd of the divisor sum and Dedekind psi"
doi: null
url: https://oeis.org/A344695
claim: "Conjecture: the set of primes that appear in the sequence is A065091 (the odd primes)."
strata_touched:
  - D5/S3/Arith/Divisors/OeisA344695GcdSigmaPsiPrimes
license: citation-only
triage: anchor
---

## Verified locator

Source: https://oeis.org/A344695 (revision 39, NAME and COMMENTS; unpaginated).

Dedekind psi definition: https://oeis.org/A001615 (NAME; unpaginated).

## Source statements

A344695 NAME:

> a(n) = gcd(sigma(n), psi(n)), where sigma is the sum of divisors function, A000203, and psi is the Dedekind psi function, A001615.

A344695 COMMENTS:

> Conjecture: the set of primes that appear in the sequence is A065091 (the odd primes).

A001615 NAME:

> Dedekind psi function: n * Product_{p|n, p prime} (1 + 1/p).

For each natural prime q, the conjecture says that there is a positive natural
index n with a(n) = q if and only if q is odd. The natural-number expression
for psi is `(n / ∏ p ∈ n.primeFactors, p) * ∏ p ∈ n.primeFactors, (p + 1)`;
the division is exact for positive n. The value at zero is outside the sequence.

The proof excludes 2 by the square/nonsquare divisor-sum dichotomy and constructs
every odd prime q at an index q²r^(q−1), with r prime and congruent to 1 modulo
q(q + 1)(q² + q + 1). It determines neither the first occurrence of q nor the
composite values of the sequence.

## Experimental reference

The independent arithmetic checks are in
[trureturing-experiments](https://github.com/the-omega-institute/trureturing-experiments/tree/579c9e22945b4ac6f0fbe32e55ce7fd7c28d4407/docs/reports/oeis-a344695-gcd-sigma-psi).
The file `check.py` has SHA-256
`bbb350936c12eca673642129e7b622b8234644aeb743a8787e136a56c19d521c`.
The command `python3 check.py 2000000 200` exits 0 and reports `RESULT PASS`:
the published data agree, the exclusion and square/nonsquare dichotomy hold
through 2,000,000, and the constructions for all 45 odd primes up to 200 agree.
These finite checks support the arithmetic encoding; the universal assertion
is proved in Lean.

## Literature boundary

The source and prior-art screen are recorded in
[preregistration #18688](https://github.com/the-omega-institute/trureturing/issues/18688).
Completeness and freshness of that screen are ASSUMED-UNVERIFIED.
