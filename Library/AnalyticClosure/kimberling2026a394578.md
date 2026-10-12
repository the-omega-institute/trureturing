---
bibkey: kimberling2026a394578
authors: Clark Kimberling
year: 2026
title: "A394578: a(n) = 2^(2*n-1) * p(n, n+1/2), where p(n,x) is the Lagrange interpolating polynomial through (1,0) and (k,1) for k=2..n+1"
doi: null
url: https://oeis.org/A394578/internal
claim: "The entry asserts that the consecutive ratio tends to one quarter for its moving-point Lagrange interpolation sequence."
strata_touched:
  - D5/S3/Analytic/Interpolation/OEISA394578RatioRefutation
license: citation-only
triage: anchor
---

# The moving-point Lagrange interpolation sequence

## Locator

https://oeis.org/A394578/internal, revision 36, Jun 30 2026 07:20:52.
The NAME line is:

> a(n) = 2^(2*n-1) * p(n, n+1/2), where p(n,x) is the Lagrange interpolating polynomial through (1,0) and (k,1) for k=2..n+1.

The selected COMMENT line is:

> Conjecture: a(n+1)/a(n) -> 1/4.

The entry's displayed program uses `(1/2) 4^n p[n,n+1/2]` and includes
`n=0`. Its initial terms are `0,1,9,30,133,498`. The independent
D-finiteness comment is outside the selected assertion.

## Definition correspondence

For natural n, use rational nodes `i+1` for `i` in `range(n+1)` and
values zero at `i=0`, one elsewhere. `Lagrange.interpolate` supplies
the polynomial of degree at most n at these distinct nodes. The source
index k is exactly `i+1`. There is no shift in n or in the ratio.

The rational coefficient `4^n/2` equals the source normalization and
preserves `a(0)=0`; no natural exponent subtraction occurs. Rational
values are embedded in the reals before division and convergence at
`atTop`. Although Lean division is total, the proof establishes
`a(n)>0` for every `n>=1`, so the entire relevant tail has ordinary
nonzero denominators. The value assigned to the ratio at zero has no
bearing on convergence.

## Suppliers and conclusion

Pinned Mathlib supplies `Lagrange.sum_basis`, the native interpolation
construction, its nodal evaluations and degree bound, finite product
reindexing and bounds, and `ge_of_tendsto`. The interpolation sum is
one minus the basis polynomial attached to the first node. At the
moving point, reverse the numerator factors and compare their absolute
values with the denominator factors. This gives an error at most one
half, so the evaluated interpolant lies between one half and three
halves. After normalization, every tail ratio is at least four thirds.
This excludes the printed limit of one quarter.

The formal result is the negation of this limit assertion only. No
correct limit, recurrence, integrality or D-finiteness result is claimed.

## Literature search boundary

The exact entry identifier and its one-quarter assertion were searched
on ordinary web results and unrestricted-language GitHub code results.
The source entry was found; jOEIS and LODA programs were found, without
a universal proof connecting their formulas to the native interpolation
definition. No exact published settlement was found in that searched
scope. Repository D5 declarations, including private originals, Library,
Problems and the supplied all-state issue/PR search contained no exact
settlement. Issue #9109 concerns the different fixed evaluation
sequences A396722, A396723 and A396724. The Mathlib and installed Lean
package search likewise found no A394578-specific declaration.
These are bounded search results, not a claim of global absence.
