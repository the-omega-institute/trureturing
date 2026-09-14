---
bibkey: bala2022egfgeneral
authors: Peter Bala
year: 2022
title: "Bala's general totient-period conjecture for integral G(exp(x) - 1)"
doi: null
url: https://oeis.org/A305550
claim: "More generally, we conjecture that the same property holds for integer sequences having an e.g.f. of the form G(exp(x) - 1), where G(x) is an integral power series. The property is eventual periodicity modulo every positive k with period dividing phi(k)."
strata_touched:
  - D5/S1/Recurrence/Periodic/IntegralEgfTotientPeriod
license: citation-only
triage: anchor
---

# Bala's general exponential generating function conjecture

Peter Bala's July 8, 2022 comment on A305550 contains the broader conjecture
quoted above. The same broader conjecture appears on A004123. These are two
locations of one conjecture, which this module settles once, not twice.

For any integral coefficient function g, let G be the rational power series
with coefficients g(k). The module proves that n! times the coefficient of
x^n in G(exp(x) - 1) equals the integer sum of g(k) k! S(n,k) for k at most n.
In particular, all these factorial-scaled coefficients are integers; no separate
integrality hypothesis is needed. The imported weighted Stirling-transform
theorem gives period phi(m) modulo m from n at least m for every positive m.
The integer sequence is extracted from the rational coefficients and proved
equal to T(g,n); it is not assumed to satisfy an unproved coefficient recurrence.

## Verified locator

- URL: https://oeis.org/A305550
- Locator: Peter Bala's July 8, 2022 COMMENT, beginning "More generally".
- Duplicate location of the same conjecture: https://oeis.org/A004123
