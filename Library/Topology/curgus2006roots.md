---
bibkey: curgus2006roots
authors: Branko Ćurgus and Vania Mascioni
year: 2006
title: Roots and polynomials as homeomorphic spaces
doi: 10.1016/j.exmath.2005.07.001
url: https://faculty.curgus.wwu.edu/Papers/25RootsPolysHomSp.pdf
claim: Fixed-degree monic complex polynomials and their root multisets are homeomorphic for the coefficient maximum metric and optimal root matching metric.
strata_touched:
  - D5/S3/Analytic/ClosedLowerHalfPlaneFactorContinuity
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1016/j.exmath.2005.07.001.
Author PDF: https://faculty.curgus.wwu.edu/Papers/25RootsPolysHomSp.pdf.
Theorem 2.4, page 82, and Theorem 4.4, page 91.

## Topological correspondence

Theorem 2.4, page 82, gives continuity of the inverse of a continuous bijection
between metric spaces when closed bounded subsets of its domain are compact
and the inverse takes bounded sets to bounded sets. Theorem 4.4, page 91,
identifies monic polynomials and root multisets homeomorphically. Multiplicities
are retained. The article fixes degree at least two and identifies degree one
as an immediate special case.

These are topological antecedents of the compact root-tuple argument in
ClosedLowerHalfPlaneFactorContinuity. Its finite coefficient image lies in
complex dimension twice the factor degree plus one, with the induced topology.
Sequential compactness is used on this metrizable image, and the resulting
continuous factor coefficients are pulled back to an arbitrary parameter space.
The half-plane boundary uniqueness needed to identify a tuple limit is an
additional scalar factorization input. The Lean proof includes degree zero
and does not import a formalization of the article.
