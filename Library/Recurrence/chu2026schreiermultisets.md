---
bibkey: chu2026schreiermultisets
authors: Hùng Việt Chu; Yubo Geng; Julian King; Steven J. Miller; Garrett Tresch; Zachary Louis Vasseur
year: 2026
title: "Linear Recurrences from Counting Schreier-Type Multisets"
doi: 10.5281/zenodo.19949535
url: https://math.colgate.edu/~integers/aa53/aa53.pdf
claim: "Section 5 conjectures the recurrence for the cardinalities of A^(2)_(1,2,n)."
strata_touched:
  - D5/S1/Recurrence/ChuSchreierMultisetRecurrenceQTwo
license: citation-only
triage: anchor
---

# Linear Recurrences from Counting Schreier-Type Multisets

Section 5, "Further Investigations", defines the multiset families and lists five
conjectured recurrences. The definition on printed page 19 reads:

> Define
> \(A^{(s)}_{p,q,n} := \{F \subset \{1, \ldots, 1, \ldots,
> n-1, \ldots, n-1, n\} : n \in F \text{ and } q\min F \ge p|F|\}.\)

The two repeated ranges are underbraced by \(s\) in the printed display: each
of \(1,\ldots,n-1\) has multiplicity \(s\), while \(n\) has multiplicity one.
The first item under "Below are the data and conjectured recurrences we gather"
reads on the same page:

> 1. \((|A^{(2)}_{1,2,n}|)^{\infty}_{n=1}: 1, 2, 4, 9, 19, 41,
> 88, 189, 406, 872, 1873, 4023, 8641, \ldots\) with
> \(a_n = a_{n-1} + 2a_{n-2} + a_{n-3};\)

The formal reading uses sub-multisets of the displayed ground multiset, with
cardinality counting multiplicity. It specializes \((p,q)=(1,2)\), so the
condition is \(2\min F \ge |F|\). Since the paper does not state a starting
index for the recurrence, the formal statement starts at \(n=4\), the least
index for which all four displayed sequence indices are at least one.

The other four recurrences on printed pages 19-20 and the preceding double-sum
formula are not asserted by this formalization.

## Verified locator

- DOI: https://doi.org/10.5281/zenodo.19949535
- URL: https://math.colgate.edu/~integers/aa53/aa53.pdf
- Locator: Section 5, "Further Investigations", printed page 19.
