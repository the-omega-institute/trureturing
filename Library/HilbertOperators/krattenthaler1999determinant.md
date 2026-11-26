---
bibkey: krattenthaler1999determinant
authors: Christian Krattenthaler
year: 1999
title: Advanced Determinant Calculus
doi: 10.48550/arXiv.math/9902004
url: https://arxiv.org/abs/math/9902004
claim: "Equation (2.7) evaluates the determinant of the reciprocal pairwise-sum matrix as two ordered difference products divided by the product of all pairwise sums."
strata_touched:
  - D5/S3/Arith/Lattices/HilbertSmith/CauchyDeterminant
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.math/9902004

Source: https://arxiv.org/abs/math/9902004

The displayed identity is equation (2.7) in §2.1 on PDF page 6.

## Cauchy's determinant

Equation (2.7) in §2.1 gives the Cauchy determinant identity. The two
difference products in the Lean statement reverse the order of subtraction
in both variables. The resulting signs cancel. The Lean statement uses
arrays over an arbitrary field and requires every pairwise sum to be nonzero.
