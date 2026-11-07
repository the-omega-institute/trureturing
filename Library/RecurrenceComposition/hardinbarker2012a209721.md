---
bibkey: hardinbarker2012a209721
authors: R. H. Hardin; Colin Barker
year: 2012
title: "OEIS A209721: three-column arrays with distinct clockwise edge differences"
doi: null
url: https://oeis.org/A209721/internal
claim: "The literal three-column array count satisfies the empirical recurrence and Barker's empirical formal generating function."
strata_touched:
  - D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209721EdgeDifferences
license: citation-only
triage: anchor
---

# Hardin and Barker, OEIS A209721

## Verified locator

DOI: null

Source: https://oeis.org/A209721/internal

OEIS A209721, revision 43, is the source. NAME and FORMULA identify the
following quotations; the entry has no page numbers, DOI or arXiv identifier.
Hardin's entry is dated March 12, 2012; Barker's generating function is
dated March 23, 2012.

## Source statement

> 1/4 the number of (n+1) X 3 0..2 arrays with every 2 X 2 subblock having distinct clockwise edge differences.

> Empirical: a(n) = a(n-1) +2*a(n-2) -2*a(n-3).

> Empirical g.f.: x*(3+x-5*x^2)/((1-x)*(1-2*x^2)). [_Colin Barker_, Mar 23 2012]

Offset 1,1 restricts the source domain to positive indices. For a square
with top row a,b and bottom row c,d, differences are b-a,d-b,c-d,a-c in
the integers. All labelled arrays are counted without symmetry quotients;
one quarter means division by rational four.

## Mathematical scope

The count uses Matrix (Fin (n+1)) (Fin 3) (Fin 3), with the signed-difference
list tested in every consecutive square. The recurrence covers every index
at least four. The ordinary series has zero constant term and the stated
positive-index coefficients. Its existence and cross-multiplied generating
identity are conclusions. The formal denominator has constant term one;
no analytic convergence assumption is involved.

Reading the rows identifies arrays with walks in a 27-state compatibility
graph. The all-length finite-relation count and transfer-vector recurrence
yield the source recurrence. Initial counts and coefficient extensionality
yield the formal-series identity. The signed-square predicate is shared
with the five-column formalization; that result alone does not give this
three-column count.

## Computed evidence and limits

The independent exact checker is in
https://github.com/the-omega-institute/trureturing-experiments at commit
`fc319fd926e2340f6c568cf498fb820357e4be36`, under
`docs/reports/hardin-barker-a209721/`. Its `check.py` SHA-256 is
`33f37f5145a55bed5c8bde97c74917e2a6f640b2e6ce35ff88eefe2998eaf704`.
The recorded command is `python3 check.py`, exit 0, with final output
`ALL_CHECKS_OK`. It matches all 210 b-file values, direct enumeration at
indices 1,2,3, and the recurrence and generating-function convolution
through coefficient 210. These finite readings do not prove an unbounded
identity. Parity formulas, Peterson's two-step recurrence, other widths
and analytic convergence are not additional Lean conclusions here.

The bounded literature screen is recorded in preregistration issue
https://github.com/the-omega-institute/trureturing/issues/23890.
Completeness is ASSUMED-UNVERIFIED, including unavailable literature indexes.
OEIS text and data are attributed to the OEIS Foundation and contributors
under CC BY-SA 4.0. No source program is reproduced.
