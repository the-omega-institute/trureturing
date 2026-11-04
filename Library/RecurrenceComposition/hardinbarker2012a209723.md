---
bibkey: hardinbarker2012a209723
authors: R. H. Hardin; Colin Barker
year: 2012
title: "OEIS A209723: five-column arrays with distinct clockwise edge differences"
doi: null
url: https://oeis.org/A209723/internal
claim: "The five-column labelled-array count satisfies Barker's two parity formulas, the empirical third-order recurrence and the conjectured rational generating function."
strata_touched:
  - D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209723EdgeDifferences
license: citation-only
triage: anchor
---

# Hardin and Barker, OEIS A209723

## Verified locator

Source: https://oeis.org/A209723/internal

The source is OEIS A209723, revision 11. Hardin submitted the entry in 2012;
Barker's FORMULA contribution is dated July 12, 2018. The entry has no page
numbers, DOI, or identified source-paper arXiv identifier. NAME and FORMULA
are the locators for the following verbatim quotations.

## Source statement

> 1/4 the number of (n+1) X 5 0..2 arrays with every 2 X 2 subblock having distinct clockwise edge differences.

> Empirical: a(n) = a(n-1) + 2*a(n-2) - 2*a(n-3).

```text
Conjectures from _Colin Barker_, Jul 12 2018: (Start)
G.f.: x*(6 + x - 11*x^2) / ((1 - x)*(1 - 2*x^2)).
a(n) = 3*2^(n/2 - 1) + 4 for n even.
a(n) = 2^((n + 1)/2) + 4 for n odd.
(End)
```

Offset 1,1 gives the positive index domain. For a square with top row a,b
and bottom row c,d, the signed integer differences are b-a,d-b,c-d,a-c.
All labelled arrays are counted; division by rational four does not mean
quotienting by symmetries. Five columns correspond to column four of the
parent entry A209727.

## Mathematical scope

The formal count uses Matrix (Fin (n+1)) (Fin 5) (Fin 3) and tests every
consecutive square. The parity formulas cover every positive index, the
recurrence covers indices at least four, and the generating identity holds
in rational formal power series. Its denominator has constant term one.

Andrew's answer https://math.stackexchange.com/a/4995628 supplies the local
eight-square classification for the related four-column problem A209722.
The five-column proof uses that classification in an exact row adjacency
table and an induction on arbitrary walk length. That partial source does
not give the five-column count.

The source text is attributed to the OEIS Foundation and contributors,
CC BY-SA 4.0. No source program is reproduced. The literature screen in
issue #24091 is bounded; completeness remains ASSUMED-UNVERIFIED.
