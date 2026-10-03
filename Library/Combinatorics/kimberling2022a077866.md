---
bibkey: kimberling2022a077866
authors: Clark Kimberling
year: 2022
title: "OEIS A077866: Expansion of (1-x)^(-1)/(1-x-2*x^2+2*x^3)"
doi: null
url: https://oeis.org/A077866
claim: "Conjecture: let b(n) be the number of subsets S of {1,2,...,n} having more than one element such that (sum of least two elements of S) = max(S). Then b(0) = b(1) = b(2) = 0 and b(n+3) = a(n) for n >= 0."
strata_touched:
  - D5/S3/Combinatorics/KimberlingLeastTwoSubsetCount
license: citation-only
triage: anchor
---

# OEIS A077866

Kimberling's comment dated 27 September 2022 states the subset-count
conjecture quoted above. The official OEIS text interface returned revision
47 (30 June 2026) on 30 September 2026. The entry defines `a(n)` by
`1/((1-x)*(1-x-2*x^2+2*x^3))`; its even and odd formulas are
`a(2m)=3*2^(m+1)-2*(m+1)-3` and
`a(2m+1)=2^(m+3)-2*(m+3)`. The formal sequence uses the equivalent initial
values `1,2,5,8` and recurrence
`a(n+4)+4*a(n+1)=2*a(n+3)+a(n+2)+2*a(n)`.

The OEIS entry still labels the subset assertion a conjecture in the
source check recorded in issue #11414. This note records the wording and
sequence identification; it does not claim publication priority.

## Verified locator

- URL: https://oeis.org/A077866 (official OEIS text interface, revision 47,
  retrieved 2026-09-30; `%C` contains Kimberling's dated conjecture and
  `%F` contains the recurrence and parity formulas).
