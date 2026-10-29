---
bibkey: ku2026monochromatic
authors: Kuo-Han Ku
year: 2026
title: "Monochromatic k in a row"
doi: null
url: https://arxiv.org/html/2606.12880v1
claim: "Definitions 2.1, 2.2, 2.4, 2.6 give ordinary boards, near-line avoidance, saturation and maximum density; Conjecture 5.6 asserts D(k,[k]^d)=1-2/k for every k>=2 and natural d."
strata_touched:
  - D5/S3/Combinatorics/Geometry/KuNearLineRefutation
license: citation-only
triage: anchor
---

## Verified locator

https://arxiv.org/html/2606.12880v1, Definitions 2.1, 2.2, 2.4, 2.6 and section 5.1.2, Conjecture 5.6.

## Mathematical scope

A standard line consists of k consecutive integer points with nonzero signed
coordinate direction and all endpoints in the ordinary board. A configuration
contains no (k-1)-element subset of such a line. Saturation is maximality under
inclusion. D is the attained maximum of cardinality divided by board cardinality
among saturated configurations. The separate toric-board and minimum-density
notions are not used here.

Conjecture 5.6 quantifies over every k at least two and every natural dimension.
The three-by-three-by-three ordinary board supplies the parameter pair for the
strict upper bound D(3,[3]^3)<1/3. This bound does not assert an exact maximum or
an attaining configuration of any specified size.


## Exact conjecture and dependencies

Section 5.1.2 states: "For every $k\in\mathbb{N}_{\geq 2}$ and
$d\in\mathbb{N}$, $D(k,[k]^d)=1-\frac{2}{k}$."
The same section gives an independent two-dimensional construction and cites
Lemma 4.1 for even $k$ with $k/2$ coprime with $d!$. Its minimum-density
Question 5.7 is separate. No later theorem in v1 is stated as depending on
Conjecture 5.6.

The repository result `KuGeometry.result` refutes this universal equality via
`KuGeometry.exact_real_event`. These are repository derivations, not assertions
that the cited paper already contains the refutation. An exact maximum of
$8/27$ and a saturated size-eight attainer are not claimed.

## Bounded literature reading

The arXiv record lists v1 only. The primary v1 HTML read on 2026-10-29 has
792385 bytes and SHA-256
`6bc5cb16b8c6a9a71baf44f17e03c7361257aeba9c5c38ff4c3866283998dcb3`.
MathDB https://mathdb.com/p/375265 displays zero posted solutions; OpenAlex
https://openalex.org/W7164573657 reports zero citations. A Crossref title query
returned unrelated titles and no matching DOI. A general Google query supplied
only a redirect page. The source-cited master's thesis was not read. These are
bounded negative findings, not an exhaustive priority claim.
