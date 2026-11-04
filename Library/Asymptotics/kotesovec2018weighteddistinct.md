---
bibkey: kotesovec2018weighteddistinct
authors: OEIS Foundation Inc.; Vaclav Kotesovec
year: 2018
title: OEIS A022629 and the weighted distinct-partition logarithmic conjectures
doi: null
url: https://oeis.org/A022629
claim: The logarithms of the weighted distinct-partition coefficients have the stated ratio asymptotics for natural exponents one through five.
strata_touched:
  - D5/S0/Asymptotics/GeneratingFunctions
license: citation-only
triage: anchor
---

# Weighted distinct-partition coefficients

## Verified locator

Source: https://oeis.org/A022629

The primary source is the unpaginated OEIS entry A022629, revision 54.
The downloadable entry is https://oeis.org/search?q=id:A022629&fmt=text.
It credits the conjecture to Vaclav Kotesovec. The related entries are
https://oeis.org/A092484, https://oeis.org/A265840,
https://oeis.org/A265841 and https://oeis.org/A265842.
No paper, DOI, arXiv identifier or page number is supplied for these conjectures.

## Source statements

OEIS A022629, NAME:

> Expansion of Product_{m>=1} (1 + m*q^m).

OEIS A022629, FORMULA:

> Conjecture: log(a(n)) ~ sqrt(n/2) * (log(2*n) - 2).

The formula is attributed to Vaclav Kotesovec, May 08 2018. The entry's
comment by Vladeta Jovovic states:

> Sum of products of terms in all partitions of n into distinct parts.

OEIS A092484, NAME:

> Expansion of Product_{m>=1} (1 + m^2*q^m).

OEIS A092484, FORMULA:

> Conjecture: log(a(n)) ~ sqrt(2*n) * (log(2*n) - 2).

OEIS A265840, NAME:

> Expansion of Product_{k>=1} (1 + k^3*x^k).

OEIS A265840, FORMULA:

> Conjecture: log(a(n)) ~ 3*sqrt(n/2) * (log(2*n) - 2).

OEIS A265841, NAME:

> Expansion of Product_{k>=1} (1 + k^4*x^k).

OEIS A265841, FORMULA:

> Conjecture: log(a(n)) ~ 4*sqrt(n/2) * (log(2*n) - 2).

OEIS A265842, NAME:

> Expansion of Product_{k>=1} (1 + k^5*x^k).

OEIS A265842, FORMULA:

> Conjecture: log(a(n)) ~ 5*sqrt(n/2) * (log(2*n) - 2).

The last four conjectures are attributed to Vaclav Kotesovec, Dec 27 2020.
All five sequences start at index zero. A finite polynomial product over
1 through n gives exactly the degree-n coefficient of the infinite formal
product, since every omitted factor has constant term one and its other
term has degree greater than n. At n = 0 this coefficient is one.
The asymptotic symbol means a quotient tending to one along all natural
indices. It does not specify an additive second term or a prefactor.

## Mathematical mechanism and limits

For every fixed positive natural exponent r, expansion gives a sum of
r-th powers of products of distinct positive parts summing to n. A nearly
triangular partition contributes at least the r-th power of M factorial,
where M is maximal with M(M+1)/2 at most n. An upper bound on every product
and the estimate log q(n) at most 2 sqrt(n) yield the matching logarithmic
rate. The proof uses the existing polynomial, interval, factorial,
logarithm, square-root and filter-limit operations in pinned Mathlib.

The preregistrations are issues #21434, #21435, #21436, #21438 and #21439
of https://github.com/the-omega-institute/trureturing.
Their bounded literature screen read the indicated scopes of
arXiv:1904.08004v2, the partition-norm paper in NNTDM 31(4), 908–915,
and the exposed publisher material for DOI 10.1007/s11139-026-01350-4.
The latter main text was not read. Endpoint failures and bounded metadata
searches do not establish absence of a prior proof. Literature completeness
and priority remain ASSUMED-UNVERIFIED.

## Experiment

The finite checker is in the private repository
https://github.com/the-omega-institute/trureturing-experiments,
commit 53f0db6627014ac92ef1aa24517b52fc338485c9, under
`docs/reports/kotesovec-weighted-distinct-partition-log-asymptotics/`.
The preregistration reports `python3 check.py`, exit 0, ending
`ALL_CHECKS_OK`, with check.py SHA-256
`efe81d3bf65c873ebd289891ca08dab21a666e6af396ae5f4cc329a70c04b2bf`.
These are finite checks; they do not prove the limit.

## License

OEIS source quotation and attribution follow the OEIS End-User License
Agreement, https://oeis.org/LICENSE. The entries and their authors are
cited for the sequence definitions and conjectures; no external proof
program is reproduced here.
