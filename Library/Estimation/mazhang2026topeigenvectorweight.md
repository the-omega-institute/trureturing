---
bibkey: mazhang2026topeigenvectorweight
authors: "Haobo Ma; Wenlin Zhang"
year: 2026
title: "Resolving Question III.5 of Stepanov–Herrmann–Guhr (arXiv:2104.08966v1, p. 7): the top-eigenvector weight gap occurs exactly above sigma = c"
doi: "10.5281/zenodo.23927428"
url: "https://doi.org/10.5281/zenodo.23927428"
claim: "Corollary 10: for real symmetric H of size n >= 3, a unit vector u, tau = tr H / n and r = u^T H u - tau > 0, a top eigenvector of weight at most 1/2 relative to u forces tr((H - tau I)^2) >= 2n r^2/(n-2); if H is positive semidefinite then u^T H u <= tr H / 2."
strata_touched:
  - D5/S3/Estimation/CenteredTopEigenvectorObstruction
license: citation-only
triage: anchor
---
<!-- GID: D5/L/Estimation/mazhang2026topeigenvectorweight -->
# Centered obstruction for the top-eigenvector weight

## Verified locator

The written proof is by **Haobo Ma and Wenlin Zhang**, version 2, exact-version DOI
https://doi.org/10.5281/zenodo.23927428, Corollary 10, Section 4. The question it resolves is
Question III.5 of Y. Stepanov, H. Herrmann and T. Guhr, arXiv:2104.08966v1, p. 7, recorded in
stepanovherrmannguhr2021correlation.

## Statement

Let H be real symmetric of size n >= 3, u a unit vector, tau = tr H / n and
r = u^T H u - tau > 0. If a top eigenvector has weight at most 1/2 relative to u, then
tr((H - tau I)^2) >= 2n r^2/(n-2). If also H is positive semidefinite, then u^T H u <= tr H / 2.
The proof generalizes the centered two-point energy argument of the note's Proposition 2: the
weight condition gives two eigenvalues whose sum is at least 2 u^T H u, and the remaining
n - 2 centered eigenvalues have sum equal to minus the sum of those two.
