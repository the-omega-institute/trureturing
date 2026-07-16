---
bibkey: hedenmalm1997hilbert
title: A Hilbert space of Dirichlet series and systems of dilated functions in L2(0,1)
doi: 10.1215/S0012-7094-97-08601-4
claim: Coefficient-space models of Dirichlet series with square-summable coordinates.
strata_touched:
  - D5/S3/Weil/LabeledZeta
license: citation-only
triage: anchor
---

# A Hilbert Space of Dirichlet Series

Hakan Hedenmalm, Peter Lindqvist, and Kristian Seip model Dirichlet series
`f(s) = sum a_n n^(-s)` through their square-summable coefficient vectors.
That coefficient-space model is the literature anchor for the labeled vector
used by `D5/S3/Weil/LabeledZeta.labeled_zeta_vector_ne_zero`.

The paper does not use the repository's ledger vocabulary or state the Lean
declaration verbatim. The formal nonvanishing result is the immediate
coordinate consequence that the identity coefficient is one.

## Search log

- 2026-07-16: Queried NyxID/Tavily for `"A Hilbert space of Dirichlet
  series and systems of dilated functions" coefficients constant term DOI`.
  The arXiv and Semantic Scholar results identified the coefficient model,
  Duke Mathematical Journal 86 (1997), pages 1-37, arXiv `math/9512211`, and
  DOI `10.1215/S0012-7094-97-08601-4`.
- 2026-07-16: Queried `Riemann zeta functional equation conjugation symmetry
  critical line Re(s)=1/2 scholarly article DOI`. Results were encyclopedia,
  video, and lecture-note pages rather than a DOI-bearing formal source, so
  the exact mirror fixed-point declaration remains `repo-derived`.
- 2026-07-16: Queried the exact phrase `"scaling ledger" zeta reflection
  "1 - conjugate"`. No scholarly match for the repository's scaling-ledger
  formulation was returned; the mirror reversal declaration is
  `repo-derived`.
- 2026-07-16: Five initial proxy attempts in the preceding search pass sent
  the JSON object with the wrong transport shape and received HTTP 422.
  Reissuing JSON on stdin with `Content-Type: application/json` produced the
  results above; no bibliographic conclusion was drawn from failed requests.

## Verified locator

- DOI: https://doi.org/10.1215/S0012-7094-97-08601-4
- arXiv: https://arxiv.org/abs/math/9512211
