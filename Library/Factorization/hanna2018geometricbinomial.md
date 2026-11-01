---
bibkey: hanna2018geometricbinomial
authors: Paul D. Hanna
year: 2018
title: "OEIS A301310, A301311 and A301432: geometric binomial averages"
doi: null
url: https://oeis.org/A301310/internal
claim: "A301310 and A301311: a(n) is divisible by 10 for n>0 (conjecture). A301432: a(n) is divisible by 21 for n>0 (conjecture)."
strata_touched:
  - D5/S3/ArithSums/HannaA301310Divisibility
  - D5/S3/ArithSums/HannaA301311Divisibility
  - D5/S3/ArithSums/HannaA301432Divisibility
license: citation-only
triage: anchor
---

## Verified locator

DOI: null. These are OEIS entries without a source DOI or arXiv identifier.

Source: https://oeis.org/A301310/internal

Related sources: https://oeis.org/A301311/internal and https://oeis.org/A301432/internal

## Source statements

A301310, COMMENTS line 2:

> a(n) is divisible by 10 for n>0 (conjecture).

A301310, FORMULA line 3:

> a(n) = Sum_{k>=0} 2^k * binomial(k^2, n) / 3^(k+1).

A301311, COMMENTS line 2:

> a(n) is divisible by 10 for n>0 (conjecture).

A301311, FORMULA line 3:

> a(n) = Sum_{k>=0} 2^k * binomial(k^2 + n-1, n) / 3^(k+1).

A301432, COMMENTS line 1:

> a(n) is divisible by 21 for n>0 (conjecture).

A301432, FORMULA line 3:

> a(n) = Sum_{k>=0} 3^k * binomial(k^2, n) / 4^(k+1).

The locators are COMMENTS and FORMULA line numbers in the internal OEIS records;
these sources have no page numbering. Each infinite sum is a convergent real
series indexed by natural numbers. Ordinary natural binomial coefficients include
zero when the upper index is below the lower index. In A301311, subtraction in
the upper index is natural subtraction. The n=0 term is one. The positive-index
claims ask for an integer quotient, so they assert integrality as well as the
stated divisibility.
