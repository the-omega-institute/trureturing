---
bibkey: bala2023quarticparity
authors: Peter Bala
year: 2023
title: "OEIS A361034 and A361035: parity of quartic factorial quotients"
doi: null
url: https://oeis.org/A361034
claim: "Conjecture: a(n) is odd iff n = 2^k - 2 for some k >= 1."
strata_touched:
  - D5/S3/Arith/FactorialRatio/BalaA361034Parity
  - D5/S3/Arith/FactorialRatio/BalaA361035Parity
license: citation-only
triage: anchor
---

# Quartic factorial quotient parity

## Verified locator

Source: https://oeis.org/A361034

Companion source: https://oeis.org/A361035
The source entries are unpaginated. The quotations are from their NAME and
COMMENTS fields in the OEIS data mirror `oeis/oeisdata` at `e7d0073e`.

## Source statements

### A361034

> a(n) = 2520*(4*n)!/(n!*(n+2)!^3).

> Conjecture: a(n) is odd iff n = 2^k - 2 for some k >= 1.

### A361035

> a(n) = 9979200 * (4*n)!/(n!*(n+3)!^3).

> Conjecture: a(n) is odd iff n = 2^k - 3 for some k >= 2.

The natural index includes zero. Natural-number division represents the source
quotient because its denominator divides its numerator. The exponent lower
bounds ensure that the natural subtractions are exact.

## Scope

The two rows have coefficients 2520 and 9979200 and shifts 2 and 3.
Their common proof compares factorial prime exponents and uses the binary digit
sum to determine parity. No conclusion about every row of A361032 is asserted.
Literature completeness is ASSUMED-UNVERIFIED beyond the sources screened in
issues #18606 and #18607.
