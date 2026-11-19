---
bibkey: gracia2026factorial
authors: Antonio Gracia Llorente
year: 2026
title: Factorial Cancellation in Polynomial Continued Fractions
doi: 10.5281/zenodo.23506866
url: https://zenodo.org/records/23506866
claim: "Theorems 5.11, 5.12 and 6.4 give prime-occurrence classifications for OEIS A363347, A363102 and A372763."
strata_touched:
  - D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity
  - D5/S3/Arith/Congruence/BourasA363102PrimeMultiplicity
  - D5/S3/Arith/Primes/BourasA372763OnceRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.5281/zenodo.23506866

Original deposited version: https://zenodo.org/records/23506866

Record metadata: https://zenodo.org/api/records/23506866

The publication date is 2026-10-20. The record creation timestamp is
2026-10-20T17:54:04.729801+00:00; its version relation has index zero.
The deposited file is `Factorial_Cancellation_Continued_Fractions.pdf`
(28 pages, 1,487,091 bytes), with Zenodo checksum
`md5:061096e24b8cf91dd05397fa4a34180b`.

## Statements and correspondence

The paper defines the same reciprocal continued fraction in equation (1),
with positive reduced denominator and indices $n\ge3$. Equation (2) uses
terminal $-c$ for the quadratic families and $n+m-1$ for the linear families.

- **A363347, Theorem 5.11, equation (35), pp. 15–16:** at $c=4$, the prime
  $5$ occurs once; a prime $p\equiv1,9\pmod{10}$ occurs twice; every other
  prime is absent. In particular, every occurring prime other than $5$ has
  exactly two indices, as in `BourasA363347.result`.
- **A363102, Theorem 5.12, equation (36), p. 16:** at $c=2$, primes
  $p\equiv1,7\pmod8$ occur twice, with a third occurrence exactly when
  $2p^2+2$ is a square; every other prime is absent. The third index satisfies
  $n^2-2p^2=2$. This includes the count asserted by `BourasA363102.result`
  and supplies a converse not formalized by that declaration. The paper's
  rejection of the literal assertion about all primes is compatible with
  the repository's explicit restriction to primes that occur.
- **A372763, Theorem 6.4, equation (48), p. 20:** at $m=6$, primes $2$ and
  $3$ are absent, $11$ occurs exactly twice at indices $10$ and $21$, and
  every other prime at least $5$ occurs exactly once. This contains the
  repeated-$11$ witness used by `BourasA372763OnceRefutation.result` and
  also gives a global classification not formalized by that refutation.

## Bibliographic scope

This deposited version is an earlier reference for the corresponding
repository proof records. The A372763 module first appears in commit
`2051b723ea335883f43eb9e7e940dad3f3da0fae` (2026-10-26); the A363347 and
A363102 modules first appear in
`235becf77fbe7f7697e467acf792ff263a9ab6dc` (2026-10-29).

These are literature proofs and provenance locators. They do not extend the
statements of the repository's Lean declarations or certify the rest of the
manuscript. Priority over all other literature remains unverified.
