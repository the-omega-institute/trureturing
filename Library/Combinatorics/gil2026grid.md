---
bibkey: gil2026grid
authors: Juan Gil, Zhenni Liang, Ayodeji Odetola, Michael Weiner
year: 2026
title: Points of maximal traffic on a grid with obstruction
doi: null
url: https://arxiv.org/abs/2609.01562
claim: "Conjecture 7.4 asks whether every antidiagonal obstruction has traffic maxima at (1,1) and (n-1,n-1) for every n at least 496; Section 7 gives the binomial-ratio comparison."
strata_touched:
  - D5/S3/Arith/FactorialRatio/GridAntidiagonalTrafficBound
license: citation-only
triage: anchor
---

# Antidiagonal grid traffic

## Verified locator

- Canonical source URL: https://arxiv.org/abs/2609.01562.
- Primary version read: https://arxiv.org/html/2609.01562v1.
- arXiv identifier and submission date: 2609.01562v1, September 1, 2026.
- Exact target: Section 7, Conjecture 7.4.
- Published reduction inputs: Section 6, Propositions 7.1 and 7.2,
  Equation (2.1), Theorem 5.1 and Lemma 2.2(ii)/(iii).

## Source assertion

Source: arXiv:2609.01562v1, submitted September 1, 2026, Sections 2, 5, 6
and 7. The primary HTML is https://arxiv.org/html/2609.01562v1. This note
attests the question and the published reductions, not a published proof
of Conjecture 7.4. The existing preregistration is issue 8249:
https://github.com/the-omega-institute/trureturing/issues/8249.

The source's literal Conjecture 7.4 is:

> For every n ≥ 496 and every obstruction B on the antidiagonal x+y=n,
> the maximum of f_B is attained at (1,1) and (n-1,n-1).

The following source sentence reads “Equivalently, ρ(n)<1 for all n≥496.”
The repository adopts the strict ratio assertion only as a stronger
sufficient assertion. The verbal maximum statement allows additional ties;
no converse or uniqueness conclusion is asserted here.

## Source-to-arithmetic boundary

The Lean endpoint is the exact rational inequality for all natural n,a
with n≥496, 1≤a and 2a<n. Proposition 7.2 supplies the equality between the
boundary traffic difference and D(n)(R(n,a)-1), where D(n)>0. Proposition
7.1 supplies the opposite-candidate ties and the larger boundary competitor.
Section 6 supplies the six-point reduction for n≥9 outside the exceptional
set, whose coordinate sums 3 and 2n-3 exclude antidiagonal membership here.
Equation (2.1) handles the opposite half, Theorem 5.1 with n≥5 handles the
even central obstruction, and Lemma 2.2(ii)/(iii) handles both endpoints.
These grid/path results are literature inputs and are not Lean-verified
by the arithmetic module. The complete mathematical argument and the
all-obstruction consequence are explained in its Scribe source.

## Reuse and bounded prior-resolution search

Refreshed September 20, 2026, Asia/Singapore (September 19 UTC):

- The arXiv abstract page lists only v1. The fetched v1 HTML still states
  Conjecture 7.4 and reports rational checks only through n=2000.
- OpenAlex's first ten results for the full paper title include the source
  as W7206163366, with cited_by_count=0. The separate query
  `filter=cites:W7206163366`, page size 25, returns count=0 and no works.
- Crossref's first ten results for the full-title query contain no exact
  paper-title match or direct resolution. This is a ten-result search,
  not a conclusion about all indexed works.
- Bing's query `"2609.01562" "proof"` returned ten unrelated Microsoft
  pages. That response is unusable as prior-resolution evidence.
- Repository D5 searches for the Grid module, uniform peak bound, grid
  traffic, the n≥496 hypothesis and the Stirling step declaration found
  no existing endpoint before placement. Pinned Mathlib revision
  `db584cd6d46c92f209a44c0f1c829460d327499d` supplies
  `Stirling.log_stirlingSeq_sdiff_le`,
  `Stirling.tendsto_stirlingSeq_sqrt_pi` and
  `Stirling.le_log_factorial_stirling` (itself using
  `Stirling.le_factorial_stirling`). The proof reuses these declarations,
  binomial identities, logarithmic-series bounds and positive exponential
  Taylor sums. Robbins' stepwise bound is present in this Mathlib.
- The public Loogle query `Nat.choose, _ < 1` returned five declarations,
  all about binomially weighted geometric series, with no dominating
  all-parameter Grid inequality. This live index is not a pinned dependency
  and does not exhaust the third-party Lean ecosystem. No external Lean
  package is added.

No prior exact resolution was identified in these successful bounded
checks. Search coverage outside them, including publications absent from
the citation index, remains ASSUMED-UNVERIFIED. No worldwide priority or
new problem-count credit follows from this note.

## Repository contribution

The unbounded arithmetic proof is repository-derived. Its one private
`uniform_peak_bound` establishes the uniform analytic peak estimate and is
used directly by `result`; there is no new standalone Stirling theorem.
The mathematical Scribe's typed `Proved` resolution binds
`D5/S3/Arith/FactorialRatio/GridAntidiagonalTrafficBound.result` to
`Problems/gil-liang-odetola-weiner-antidiagonal-traffic.md`. Its full
Conjecture 7.4 consequence uses the literature-only grid implication above.
The dossier records the exact statement identity and admission
classification. Remote CI, merge, main-cache verification and completion
audit remain pending; this binding confers no problem-count credit.
