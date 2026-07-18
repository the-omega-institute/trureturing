---
bibkey: hedenmalm1997hilbert
title: A Hilbert space of Dirichlet series and systems of dilated functions in L2(0,1)
doi: 10.1215/S0012-7094-97-08601-4
claim: Square-summable Dirichlet-series Hilbert spaces, their half-plane, zeta kernel, and coefficient translations.
strata_touched:
  - D5/S3/Weil/LabeledZeta
  - D5/S3/Weil/SpectralHilbert
  - D5/S3/Weil/SpectralDynamics
  - D5/S3/Zeros/EulerWindows
  - D5/S3/Zeros/SpectralShift
license: citation-only
triage: anchor
---

# A Hilbert Space of Dirichlet Series

Hakan Hedenmalm, Peter Lindqvist, and Kristian Seip model Dirichlet series
`f(s) = sum a_n n^(-s)` through their square-summable coefficient vectors.
That coefficient-space model is the literature anchor for the labeled vector
used by `D5/S3/Weil/LabeledZeta.labeled_zeta_vector_ne_zero`.

The same model anchors the coefficient Hilbert space, the sharp
`Re s > 1/2` summability boundary, and the zeta kernel formalized in
`D5/S3/Weil/SpectralHilbert`.  The repository's mirror-resonance algebra is
an internal consequence of that kernel formula, not a claim attributed to
the paper.

It also anchors the coefficient mechanics used by
`D5/S3/Weil/SpectralDynamics`: vertical translation multiplies the `n`th
coefficient by `n^(-it)`, while a positive real translation multiplies it by
`n^(-delta)`.  Unit modulus in the first case and modulus at most one in the
second give the formal norm laws.  The paper is not cited for the repository's
unbounded-generator language, zero-resonance terminology, or unified
critical-line declaration.

The paper does not use the repository's ledger vocabulary or state the Lean
declaration verbatim. The formal nonvanishing result is the immediate
coordinate consequence that the identity coefficient is one.

The same coefficient model is contextual background for the PZG coordinate
sum and multiplicative address pullback in the two Zeros modules listed above.
The exact `PrimeAxisTable` encoding and its pointwise backward-shift identity
are repository translations, not claims attributed verbatim to the paper.

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
- 2026-07-17: Queried NyxID/Tavily for `Hedenmalm Lindqvist Seip Hilbert
  space of Dirichlet series reproducing kernel zeta s conjugate w DOI`.
  Results identified the same Duke paper, DOI, and arXiv record; the EMS
  metadata described the square-summable coefficient space, its analytic
  domain `Re s > 1/2`, and the reproducing kernel obtained by evaluating zeta
  at the summed and conjugated parameters.
- 2026-07-17: Queried `Hedenmalm Lindqvist Seip reproducing kernel zeta s
  plus conjugate w Hilbert space Dirichlet series formula`.  A later survey of
  Hilbert spaces of Dirichlet series displayed the coefficient kernel series
  and cited the Duke paper with the same DOI.  No source used the repository's
  mirror-resonance terminology, so that algebra remains `repo-derived`.
- 2026-07-17: Queried `Hedenmalm Lindqvist Seip Hilbert space Dirichlet
  series square summable coefficients analytic half plane Re s greater than
  one half`.  Independent survey and research sources explicitly attributed
  the square-summable coefficient definition and the analytic half-plane
  `Re s > 1/2` to Hedenmalm, Lindqvist, and Seip.
- 2026-07-17: Queried `"Hilbert space of Dirichlet series" translation
  semigroup imaginary translations unitary group`.  The Hedenmalm paper and a
  Dirichlet-series Hilbert-space survey were returned; the survey explicitly
  writes a vertical translate with coefficients `a_n exp(-it log n)` and
  records the coefficient norm through vertical translates.
- 2026-07-17: Queried `Dirichlet series Hilbert H2 translation operator
  f(s+sigma) contraction semigroup coefficient multiplier n power`.  The
  results again described the Hedenmalm coefficient space and vertical
  translates, together with an operator-theory abstract on isometric shift
  semigroups.  They support the coordinate multipliers, but not the source's
  stronger unbounded self-adjoint generator and reverse-domain prose.
- 2026-07-17: Queried `Riemann zeta zeros reflection conjugation quartet
  resonance reproducing kernel` and `"critical line" reflection fixed line
  unitarity self resonance l2 boundary half-density Riemann zeta`.  Results
  restated the standard reflection and conjugation symmetries, but none used
  the repository's kernel-resonance quartet terminology or combined its four
  critical-line predicates.  Those two Describe nodes are therefore
  `repo-derived`.
- 2026-07-17: Six initial NyxID/Tavily calls double-encoded the JSON request
  body and received HTTP 422.  Reissuing raw JSON on stdin with
  `Content-Type: application/json` produced the search results above; no
  bibliographic conclusion was drawn from the failed requests.
- 2026-07-18: Queried NyxID/Tavily for `Hardy space Dirichlet series
  reproducing kernel eigenvector adjoint multiplication operator prime shifts
  DOI`, `Hilbert space Dirichlet series coefficient backward shift eigenvector
  n to minus s reproducing kernel`, and the Hedenmalm-Lindqvist-Seip title with
  shift and eigenvector terms. Results confirmed the square-summable
  coefficient model, zeta reproducing kernel, multiplier setting, and the
  general adjoint-multiplier kernel-eigenvector principle. No result matched
  the repository's exact multi-axis `PrimeAxisTable` pullback or its claimed
  bundled divisibility operator, so `SpectralShift` is marked repo-derived and
  cites this note only as context.

## Verified locator

- DOI: https://doi.org/10.1215/S0012-7094-97-08601-4
- arXiv: https://arxiv.org/abs/math/9512211
