---
bibkey: coffey2007theta
authors: Mark W. Coffey
year: 2007
title: Theta and Riemann xi function representations from harmonic oscillator eigensolutions
doi: 10.1016/j.physleta.2006.10.055
claim: The completed classical zeta, its xi function, and theta-Mellin representations of the functional equation.
strata_touched:
  - D5/S3/Zeros/CompletedZeta
license: citation-only
triage: anchor
---

# Theta and Riemann Xi Function Representations

Mark W. Coffey records the completed classical zeta and develops theta-based
integral representations that extend its functional equation. This supplies a
literature anchor for the classical completed-zeta and xi facts used in
`D5/S3/Zeros/CompletedZeta`: xi is entire and is invariant under replacing
`s` by `1 - s`.

The paper does not state the repository declarations verbatim. The Lean
definition is mathlib's total pole-removed implementation, and the checked
proofs invoke mathlib's completed-zeta theorems rather than formalizing the
paper's harmonic-oscillator, Poisson-summation, or Mellin-transform derivation.
The generic zero-orbit and scaling-ledger theorem is repo-derived and is not
attributed to this source.

## Search log

- 2026-07-18: Queried NyxID/Tavily for `Riemann zeta completed xi
  functional equation analytic continuation scholarly source DOI`. Results
  located the classical completed-zeta formula and the theta/Mellin route, but
  the broad search mixed reference pages with primary and expository sources.
- 2026-07-18: Queried `M W Coffey Theta and Riemann xi function
  representations harmonic oscillator DOI` and then the exact title with
  `doi`. The IAEA INIS metadata and ScienceDirect record agreed on the title,
  journal, PII, and DOI `10.1016/j.physleta.2006.10.055`; the abstract states
  that the paper extends the zeta functional equation and develops completed
  xi representations.
- 2026-07-18: Queried the 1859 Riemann title and Titchmarsh's second-edition
  title for a DOI-bearing locator. Those searches verified the historical and
  standard-book context but did not return a DOI for either item, so the
  directly verified Coffey article is used as the machine-addressable anchor.

## Verified locator

- DOI: https://doi.org/10.1016/j.physleta.2006.10.055
- arXiv: https://arxiv.org/abs/math-ph/0612086
