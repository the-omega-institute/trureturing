---
bibkey: hardinbarker2013a228502
authors: R. H. Hardin; Colin Barker; OEIS Foundation Inc.
year: 2013
title: "OEIS A228502: corner-occupied non-attacking kings on four-column strips"
doi: null
url: https://oeis.org/A228502
claim: The two FORMULA entries give the empirical order-four recurrence and rational generating function for corner-occupied binary four-column arrays with king-neighbor exclusion.
strata_touched:
  - D5/S3/Combinatorics/TraceAvoidingArrays/HardinA228502Kings
license: citation-only
triage: anchor
---

# OEIS A228502

## Verified locator

Source: https://oeis.org/A228502

DOI: null. Revision 12 has the following NAME and both FORMULA lines. The entry has no page numbers.

> Number of n X 4 binary arrays with top left value 1 and no two ones adjacent horizontally, vertically, diagonally or antidiagonally.

> Empirical: a(n) = 2*a(n-1) + 7*a(n-2) - 2*a(n-3) - 3*a(n-4).

> Empirical g.f.: x*(1 - x)*(3 + 2*x) / (1 - 2*x - 7*x^2 + 2*x^3 + 3*x^4). - _Colin Barker_, Sep 12 2018

An immutable copy is
<https://raw.githubusercontent.com/oeis/oeisdata/77073cc8105b8042be07ec0d885da5ea5960ff3c/seq/A228/A228502.seq>,
SHA-256 `3762503b28ac2c3587fa8f074d7077629eb4723b2294962da421d3624c2d00aa`.
The offset is `1,1`. Hardin authored the sequence; Barker supplied the generating-function formula.

## Mathematical mechanism

The count is the cardinality of a filter over all maps `Fin n × Fin 4 → Bool`.
The corner is occupied and two distinct cells at maximum coordinate distance one
cannot both be occupied. All boundaries are open. At height zero there is no
corner cell, so the count is zero; at height one the count is three.

An internal continuation function uses all sixteen Boolean rows. Its initial
vector indicates horizontal exclusion. The step sums over compatible rows and
sets the value to zero at an invalid current row. Splitting the finite function
space into its first row and its tail proves the counting equality at every
positive height. The four-step vector identity propagates by linearity, giving
the recurrence for all heights at least five. Initial coefficients at heights
zero through four give the formal generating-series identity over the integers.

## Evidence boundary

The source formulas are labeled empirical in revision 12. The bounded literature
screen recorded in <https://github.com/the-omega-institute/trureturing/issues/26982>
does not establish exhaustive prior-art exclusion or worldwide priority;
those remain `ASSUMED-UNVERIFIED`. Other widths, corner-free counts and physical
interpretations are outside the result.
