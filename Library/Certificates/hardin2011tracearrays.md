---
bibkey: hardin2011tracearrays
authors: R. H. Hardin; Colin Barker
year: 2011
title: "Trace-avoiding binary arrays: OEIS A185761–A185764"
doi: null
url: https://oeis.org/A185761
claim: "Exact recurrences and generating functions for labeled binary arrays of widths two through five with unequal traces at neighboring contiguous 2 by 2 blocks; the width-two entry also states a quadratic-root closed form."
strata_touched:
  - D5/S3/Combinatorics/TraceAvoidingArrays
license: citation-only
triage: anchor
---

## Verified locator

Source: https://oeis.org/A185761

OEIS A185761, revision 8, name and formula fields (unpaginated):

```text
Number of (n+1) X 2 binary arrays with no 2 X 2 subblock trace equal to any horizontal or vertical neighbor 2 X 2 subblock trace.
Empirical: a(n) = a(n-1) + 4*a(n-2).
Conjectures from _Colin Barker_, Feb 22 2018: (Start)
G.f.: 8*x*(2 + 3*x) / (1 - x - 4*x^2).
a(n) = (2^(-n)*((1-sqrt(17))^n*(-13+3*sqrt(17)) + (1+sqrt(17))^n*(13+3*sqrt(17)))) / sqrt(17).
(End)
```

The offset is 1. Arrays are labeled functions with entries in {0,1}; a trace is the ordinary main-diagonal sum, neighbors are contiguous block origins differing by one in one coordinate, and there is no periodic boundary identification. The recurrence begins at n=3. The closed form is asserted only for n≥1; the formal generating series has zero constant coefficient.

The neighboring entries https://oeis.org/A185762, https://oeis.org/A185763 and https://oeis.org/A185764 count the same objects at widths three, four and five. Their recurrences begin at n=4, n=7 and n=10, respectively. The parent is https://oeis.org/A185769.

The experiment is in the-omega-institute/trureturing-experiments at commit 4aacaa6dcac239db3faa47e926b414bd36926b9b, docs/reports/hardin-2011-trace-avoiding-binary-arrays/check.py, SHA256 b0b3e420b409da7ffd019866e25ae1caacffe313fdf72eb785056424bf5eb979. The preregistration reports `python3 check.py`, exit 0, final line `ALL_CHECKS_OK`; this is computational evidence, not the universal proof.

Literature-search completeness is ASSUMED-UNVERIFIED. The searched scope found no published exact settlement; that is not an exhaustive novelty claim.

OEIS A185762, formula field (unpaginated):

```text
Empirical: a(n) = a(n-1) + 6*a(n-2) + a(n-3).
Empirical g.f.: 8*x*(5 + 10*x + x^2) / (1 - x - 6*x^2 - x^3). - _Colin Barker_, Apr 16 2018
```

OEIS A185763, formula field (unpaginated):

```text
Empirical: a(n) = a(n-1) + 10*a(n-2) + 3*a(n-3) - 5*a(n-4) + a(n-5) for n>6.
Empirical g.f.: 8*x*(13 + 33*x - 16*x^3 + 7*x^4 - x^5) / (1 - x - 10*x^2 - 3*x^3 + 5*x^4 - x^5). - _Colin Barker_, Apr 16 2018
```

OEIS A185764, formula field (unpaginated):

```text
Empirical: a(n) = a(n-1) + 17*a(n-2) + 9*a(n-3) - 22*a(n-4) - a(n-5) + a(n-6) - 6*a(n-7) for n>9.
Empirical g.f.: 8*x*(33 + 108*x - 43*x^2 - 249*x^3 - 69*x^4 + 5*x^5 + 43*x^6 + 81*x^7 + 18*x^8) / (1 - x - 17*x^2 - 9*x^3 + 22*x^4 + x^5 - x^6 + 6*x^7). - _Colin Barker_, Apr 16 2018
```
