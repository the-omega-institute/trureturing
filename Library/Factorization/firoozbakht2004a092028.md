---
bibkey: firoozbakht2004a092028
authors: Farideh Firoozbakht
year: 2004
title: "OEIS A092028, a(n) is the smallest m > 1 such that m divides n^m-1"
doi: null
url: https://oeis.org/A092028
claim: "A092028 %N: a(n) is the smallest m > 1 such that m divides n^m-1. A092028 %C: Each prime factor of n-1 is a solution of the equation n^x-1 == 0 (mod x), so a(n) is not greater than the smallest prime factor of n-1. Conjecture 1: All terms of this sequence are primes. Conjecture 2: a(n) is the smallest prime factor of n-1 or for n>2, A092028(n) = A020639(n-1). A092028 %A: _Farideh Firoozbakht_, Mar 26 2004. A092028 %O: 3,1"
strata_touched:
  - D5/S3/Arith/Congruence/FiroozbakhtLeastSelfDivisorPowerMinusOne
license: citation-only
triage: anchor
---

# OEIS A092028

The entry defines `a(n)` as the smallest `m > 1` such that `m` divides
`n^m-1`. The formal definition uses the natural infimum and therefore assigns
zero when the defining set is empty.

The entry records two conjectures. The formal theorem proves Conjecture 2 for
every `n > 2`; Conjecture 1 then follows from primality of the least prime
factor of `n-1`.

## Verified locator

- URL: https://oeis.org/A092028
- Locator: COMMENTS, "Conjecture 1: All terms of this sequence are primes."
- Locator: COMMENTS, "Conjecture 2: a(n) is the smallest prime factor of n-1 or for n>2, A092028(n) = A020639(n-1)."
