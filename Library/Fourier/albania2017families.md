---
bibkey: albania2017families
authors: I. N. Albania and M. Nagisa
year: 2017
title: "Some families of operator norm inequalities"
doi: 10.1016/j.laa.2017.06.030
url: https://arxiv.org/abs/1610.07302
claim: "Proposition 2.7 excludes positive definiteness of a product of sinh ratios when one numerator parameter exceeds every denominator parameter."
strata_touched:
  - D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis
  - D5/S3/Quantum/Matrix/FuruichiAmlashiHyperbolicRatio
license: citation-only
triage: anchor
---

# Products of hyperbolic sine ratios

## Locator

DOI: https://doi.org/10.1016/j.laa.2017.06.030

Preprint: https://arxiv.org/abs/1610.07302

I. N. Albania and M. Nagisa, *Some families of operator norm inequalities*,
Linear Algebra and its Applications 534 (2017), 102–121.

## Source statement

Proposition 2.7:

> Let ai, bi > 0 (i = 1, 2, . . . , n) with a1 > max{b1, b2, . . . , bn}. Then we have ∏_{i=1}^n sinh ai x / sinh bi x is not positive definite.

The product is understood with its removable value at zero,
$\prod_{i=1}^n a_i/b_i$.

## Scope

Together with classical positive definite factors and closure under
pointwise products, Proposition 2.7 gives a paper deduction of the
Furuichi–Eghbali Amlashi conjecture and the neighbouring comparison in
Remark 3.8(i). The parameter substitutions and proof sketches are in the
[problem dossier](../../Problems/furuichi-eghbali-amlashi-2022-hyperbolic-ratio-not-positive-definite.md).
These deductions are not attributed to Albania and Nagisa. The Lean
proof uses the independent analytic imaginary-axis bound; Proposition
2.7 and these product reductions are not formalized here.

## Source boundary

The quotation, bibliographic data, and locators are supplied source
information, not independently checked online in this offline seat.
The supplied literature search found no source stating the deduction of
the conjecture from Proposition 2.7 or a resolution of the conjecture;
this does not certify exhaustive coverage or priority.
