---
bibkey: ghoshbirbonshiojha2026weightedshift
authors: Arobinda Ghosh, Riddhick Birbonshi, Sarita Ojha
year: 2026
title: "On the numerical radius of a class of weighted shift operators"
doi: null
url: https://arxiv.org/abs/2608.17486v1
claim: Section 2 defines the degree-eight polynomial g and asks whether it has a unique root in (1/3,1) for all real s,t>0 and 0<q<1.
strata_touched: []
license: citation-only
triage: anchor
---

# The weighted-shift polynomial root question

## Verified locator

- Source: https://arxiv.org/abs/2608.17486v1
- Version: arXiv:2608.17486v1, submitted 18 August 2026.
- Location: Section 2, equation labeled g(z), and Open question 1.
- Source archive SHA-256: fc0cf4e3182aaca1a69a76956b5b1853e0c9dccc8478f92681e10302de39a455.

## Source assertion

> For $s,t>0$ and $0<q<1$ does the polynomial $g(z)$ have a unique root in $(\frac{1}{3},1)$?

The referenced polynomial is

$$
\begin{aligned}
g_{s,t,q}(z)={}&tq^7z^8+q^6(tq-1)z^7+3q^5(q-s)z^6+5q^4(sq-1)z^5\\
&+q^3(7q-9t)z^4+7q^2(tq-1)z^3+5q(q-s)z^2+3(sq-1)z+1.
\end{aligned}
$$

The source proves uniqueness in a restricted Case 1 and cites a known
factorization when s=t. Neither restriction belongs to Open question 1.
Its Section 3 concerns an entire function for operator numerical radius;
that entire-function statement is distinct from this polynomial question.

## Literature boundary

The bounded qualification includes the primary full article, current arXiv
metadata and title/author searches, accessible full-text screens of
arXiv:2609.31231v1 and arXiv:2609.14662v1, and Crossref relevance metadata
for publications from 2024 through 8 October 2026. No settlement of the
exact unrestricted polynomial assertion was identified in those readings.
This is a bounded search result, not a universal absence or originality claim.

The predecessor of Chakraborty and Ojha, JMAA 543(2), article 129021,
DOI 10.1016/j.jmaa.2024.129021, is identified by metadata. Its original
full text remains unread because the checked publisher route was inaccessible.
The present paper's account of its s=t result does not replace verification
of the predecessor's complete theorem scope.

## License and formalization boundary

The arXiv source carries the nonexclusive distribution license
http://arxiv.org/licenses/nonexclusive-distrib/1.0/.
This note cites the mathematical statement. No author TeX, MATLAB program,
operator implementation or other source software is vendored.
The Lean development independently formalizes the scalar polynomial question
and uses the repository's pinned Mathlib calculus and order-topology results.
