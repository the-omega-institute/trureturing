---
bibkey: bouras2023continuedfractionmultiplicity
authors: M. Bouras
year: 2023
title: OEIS A363347 and A363102, prime multiplicities of continued-fraction denominators
doi: null
url: https://oeis.org/A363347
claim: "Conjecture 3: Except for 5, the primes all appear exactly twice."
strata_touched:
  - D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity
  - D5/S3/Arith/Congruence/BourasA363102PrimeMultiplicity
license: citation-only
triage: anchor
---

## Verified locator

Source: https://oeis.org/A363347

Related source: https://oeis.org/A363102

## Statements

OEIS A363347, NAME (unpaginated):

> Denominator of the continued fraction 1/(2-3/(3-4/(4-5/(...(n-1)-n/(-4))))).

OEIS A363347, COMMENTS, Conjecture 3 (unpaginated):

> Conjecture 3: Except for 5, the primes all appear exactly twice.

OEIS A363102, NAME (unpaginated):

> Denominator of the continued fraction 1/(2-3/(3-4/(4-5/(...(n-1)-n/(-2))))).

OEIS A363102, COMMENTS, Conjecture 2 (unpaginated):

> Conjecture 2: All prime numbers appear either twice (same as A356247 and A357127) or three times.

In both statements the primes are the prime values that occur, and indices start
at three. The first claim excludes five. The second asserts a count of two or
three; it does not assert that every prime occurs. The continued fraction is a
right fold over integers from two through n-1, with rational values, followed by
a reciprocal and its positive reduced denominator.

## Scope

The formal results prove the stated occurrence counts. The shared denominator
identity applies to every negative integer terminal value. For A363102, an index
at least the occurring prime satisfies n squared = 2p squared + 2. The converse,
the full Newman–Shanks–Williams characterization, and infinitude of primes with
three occurrences remain open here.

The literature screen in issues #18626 and #18627 covers the OEIS entries,
Adamczewski's arXiv:2608.11941 and the named formal-conjecture collections.
Completeness is ASSUMED-UNVERIFIED.
