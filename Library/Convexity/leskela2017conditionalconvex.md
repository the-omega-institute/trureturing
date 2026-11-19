---
bibkey: leskela2017conditionalconvex
authors: Lasse Leskelä and Matti Vihola
year: 2017
title: "Conditional convex orders and measurable martingale couplings"
doi: 10.3150/16-BEJ827
url: https://arxiv.org/abs/1404.0999
claim: "Finite-first-moment convex order is characterized by martingale couplings; the scalar construction uses synchronized quantile-bin means and uniform absolute tails."
strata_touched:
  - D5/S3/Analytic/Probability/NoncompactQuantile
  - D5/S3/Analytic/Probability/NoncompactStrassen
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.3150/16-BEJ827

Source: https://arxiv.org/abs/1404.0999

Version: arXiv:1404.0999v3, Theorems 1.1 and 1.2, Section 2.1,
and Lemmas 3.2–3.5.

## Mathematical scope

Theorems 1.1 and 1.2 characterize convex order for probability laws and
random vectors with finite first moments by the existence of a martingale
coupling. The source treats a more general vector and conditional setting.
The delivered theorem is scalar and unparameterized, and does not assert
the stronger conditional-family or process results.

The real-valued convex tests in the delivered equivalence are required to
be absolutely integrable under both laws. This still includes every hinge
x maps to max(x-z,0), because the identity is integrable. Stop-loss order
and equal means therefore supply the scalar construction. The reverse
implication uses conditional Jensen only on these integrable tests.

The proof uses the existing generalized quantile and finite martingale
suppliers. Equal-quantile-bin means have exactly preserved means,
monotone atom lists and prefix integrals. Their actual finite-law tails
satisfy the bound Tail(mu[n],R) at most twice Tail(mu,R/2), and their
bounded-continuous integrals converge by shrinking bins and dominated
convergence. These statements provide ordered finite martingale laws with
genuine uniform first-moment tails. Pinned Prokhorov compactness,
weak-limit marginals, first-moment test closure and conditional Jensen
complete the scalar equivalence.

The host proof is an application and extension of classical approximation
methods, not an originality claim or a verbatim Lean supplier from the
article. No article source code is copied. The reused attributed compact
quantile-bin and weighted-measure Lean arguments retain the Econlib
Apache-2.0 attribution and license identified in
`lyng2026compactstrassen.md`.
