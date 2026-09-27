---
bibkey: lin2018catalanpowers
authors: Gwo Dong Lin
year: 2018
title: "On Powers of the Catalan Number Sequence"
doi: 10.1016/j.disc.2018.05.009
url: https://arxiv.org/abs/1711.01536v3
claim: "Equation (3), Theorem 1, and Lemma 2 provide the Catalan moment law and the product-density route for powers of Catalan moments."
strata_touched:
  - D5/S3/Constants/Moments/CatalanSquareHankelGrowth
  - D5/S3/Constants/Moments/CatalanSquareHankelLimits
license: citation-only
triage: anchor
---

# Lin's Catalan moment and product laws

## Verified locator

The supplied primary-source audit read https://arxiv.org/abs/1711.01536v3
(DOI 10.1016/j.disc.2018.05.009) and identifies page 3, Equation (3), page 4,
Theorem 1, and page 7, Lemma 2 as the relevant passages. Equation (3) gives
the classical Catalan probability density on `(0,4)`. Theorem 1 treats
positive powers of the Catalan moment sequence, and Lemma 2 supplies the
density formula for a product of independent positive random variables.

Consequently, if independent random variables `X` and `Y` have the Catalan
law, then `Z=X*Y` is supported on `(0,16)`, has moments
`E[Z^m]=C_m^2`, and has a density positive throughout that open interval.
The formal proof uses the equivalent scaled beta law directly and evaluates
its moments inside Lean. It does not import Lin's analytic derivation as a
formal premise.

## Scope

The equation and theorem locators above are inherited from the supplied
source audit; this metadata pass did not independently reread the paper.
The note attributes the classical moment/product route and does not claim
that Lin states either OEIS Hankel limit or the repository's elementary
Chebyshev-Gram proof.
