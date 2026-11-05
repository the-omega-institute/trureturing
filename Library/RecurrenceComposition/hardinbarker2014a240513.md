---
bibkey: hardinbarker2014a240513
authors: R. H. Hardin; Colin Barker; OEIS Foundation Inc.
year: 2014
title: "OEIS A240513: binary ladders with no exactly-two equal neighbors"
doi: null
url: https://oeis.org/A240513
claim: The first two FORMULA entries give the empirical order-five recurrence and rational generating function for the first-entry-zero binary two-column array count.
strata_touched:
  - D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240513Ladder
license: citation-only
triage: anchor
---

# OEIS A240513

## Verified locator

Source: https://oeis.org/A240513

DOI: null. The locators are the NAME and first two FORMULA fields in
revision 11, together with OFFSET. The entry has no page numbers.

## Source statement

The source is revision 11, with locators NAME, the first two FORMULA entries,
and OFFSET. The entry has no page numbers. An immutable copy is
<https://raw.githubusercontent.com/oeis/oeisdata/77073cc8105b8042be07ec0d885da5ea5960ff3c/seq/A240/A240513.seq>,
SHA-256 `4abcfcca3e6714a9e52a789a66c275239dcfa7c81002484667776b8f76d329df`.
Hardin authored the sequence; the generating-function entry is attributed
to Barker in 2018.

> Number of n X 2 0..1 arrays with no element equal to exactly two horizontal and vertical neighbors, with new values 0..1 introduced in row major order.

> Empirical: a(n) = 2*a(n-1) + a(n-2) - a(n-3) - 2*a(n-4) + a(n-5).

> Empirical g.f.: x*(2 - x)*(1 - x^2 - 2*x^3) / ((1 - x)*(1 - x - 2*x^2 - x^3 + x^4)).

The offset is `1,1`. The alphabet is binary, so introduction of new values
in row-major order is equivalent to requiring the first entry to be zero.
Rows and columns remain labeled. All neighbors lie in the open rectangle;
there is no wrapping and no diagonal adjacency. The value one need not occur.

## Mathematical mechanism

The formal count is a `Finset.card` of a filter on every map
`Fin n × Fin 2 → Bool`. Its predicate adds the equal-valued cell in the other
column and the in-bounds equal-valued cells in the preceding and following
rows. Each resulting count must differ from two. An existential first-row
condition gives count zero at height zero, while height one has count two.
The generating series therefore has zero constant coefficient and the
literal count in every positive degree. Signed subtraction is in the integers.

The internal transfer has sixteen ordered row-pair states. Its terminal
vector checks the last boundary row. The continuation sum checks each
interior row, and the initial functional checks the first boundary row and
the pinned first entry. A finite-function decomposition proves equality
with the literal board count at every height at least two. The vector
relation `v5 = 2 v4 + v3 - v2 - 2 v1 + v0` propagates by linearity.
The first six positive counts settle the recurrence at height six;
coefficient comparison gives the formal generating-function identity.

## Evidence boundary

The transfer method is classical. The bounded literature screen in
<https://github.com/the-omega-institute/trureturing/issues/26893> does not
establish exhaustive prior-art exclusion or worldwide priority; those remain
`ASSUMED-UNVERIFIED`. The relation with A105309 and other widths are outside
the stated result.
