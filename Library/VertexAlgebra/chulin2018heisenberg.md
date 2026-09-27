---
bibkey: chulin2018heisenberg
authors: Yanjun Chu and Zongzhu Lin
year: 2018
title: Moduli spaces of conformal structures on Heisenberg vertex algebras
doi: null
url: https://arxiv.org/abs/1812.11378v1
claim: Section 3.1 gives the complex Heisenberg mode bracket, vacuum Fock representation, and normalized field expansion.
strata_touched:
  - D5/S3/VertexAlgebra/HeisenbergFockPolynomial
  - D5/S3/VertexAlgebra/HeisenbergModeLocality
license: citation-only
triage: anchor
---

<!-- GID: D5/L/VertexAlgebra/chulin2018heisenberg -->

# Heisenberg Fock construction

Chu and Lin, Section 3.1, define the affine Heisenberg bracket and the
charge-zero vacuum representation over the complex numbers. Their field
notation is $Y(h,z)=\sum_{n\in\mathbb Z}h(n)z^{-n-1}$.

The repository represents the rank-one charge-zero case over $\mathbb Q$ on
$\mathbb Q[X_0,X_1,\ldots]$: negative modes multiply by variables, positive
modes act by scaled partial derivatives, and the zero mode vanishes. These
formulas give the bracket and the vacuum-generated polynomial span. The
pointwise Laurent truncation and construction using Mathlib's
`VertexOperator.of_coeff` are formalization steps in the repository, not
claims attributed verbatim to Chu and Lin.

## Verified locator

- arXiv:1812.11378v1, Section 3.1:
  https://arxiv.org/abs/1812.11378v1
- The arXiv metadata and Section 3.1 source HTML were inspected on
  28 September 2026. The source is over $\mathbb C$; the repository's
  rational polynomial realization is an algebraic specialization.
