---
bibkey: greathouse2012a175406
authors: Charles R Greathouse IV; Zak Seidov
year: 2012
title: "OEIS A175406, The greatest integer k such that (1+1/n)^k <= 2"
doi: null
url: https://oeis.org/A175406
claim: "A175406 %N: The greatest integer k such that (1+1/n)^k <= 2. A175406 %C: The sequence of first differences consists of zeros and ones, with no two consecutive zeros and no more than three consecutive ones. A175406 %F: a(n) = n log 2 + O(1). Conjecture: a(n) = floor((n + 1/2) log 2). - _Charles R Greathouse IV_, Apr 03 2012 A175406 %A: _Zak Seidov_, May 01 2010"
strata_touched:
  - D5/S0/Certificates/GreathouseLogTwoFloorRefutation
license: citation-only
triage: anchor
---

# OEIS A175406

The entry asks for the greatest integer k such that (1+1/n)^k <= 2.

The entry records Greathouse's conjecture that the value is
floor((n + 1/2) log 2).

## Verified locator

- URL: https://oeis.org/A175406
- Locator: FORMULA, "Conjecture: a(n) = floor((n + 1/2) log 2). - _Charles R Greathouse IV_, Apr 03 2012"

The conjecture holds for all n <= 10^4 in the b-file and fails at
n₀ = 1121626023352383, the counterexample certified here; no earlier published
counterexample was found in the searched surfaces (bounded search) and neither
priority nor minimality is claimed.
