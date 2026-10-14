---
bibkey: holtznazarovperes2011smoothcoins
authors: Olga Holtz; Fedor Nazarov; Yuval Peres
year: 2011
title: "New Coins from Old, Smoothly"
doi: 10.1007/s00365-010-9108-5
url: https://arxiv.org/abs/0808.1936v3
claim: "Lorentz operators, polynomial reproduction and endpoint-sensitive Bernstein bounds for the inverse central-moment correction polynomials."
strata_touched:
  - D5/S3/Analytic/SeriesInequalities/LorentzLocalCoefficientKernel
  - D5/S3/Analytic/SeriesInequalities/LorentzCoefficientRemainder
license: citation-only
triage: anchor
---

# Lorentz correction polynomials and Bernstein coefficients

The paper defines the Lorentz operators by the central-moment recurrence in
Section 4, equations (27)--(29). Lemma 14 gives exact reproduction of
polynomials of degree at most the truncation order. Corollary 16 bounds both
ends of the Bernstein coefficient array of each correction polynomial.
Its coefficients use the unnormalized basis; division by the corresponding
binomial coefficient converts them to the normalized basis used here.

The normalized correction bound in `LorentzLocalCoefficientKernel` is a
form of Corollary 16. The complex-polynomial reproduction statement in
`LorentzCoefficientRemainder` is the scalar extension of Lemma 14.
The weighted hypergeometric estimate and the estimate for arbitrary legal
local jets are repository deductions using this correction bound. Lemma 24
provides related coefficient control for smooth functions, but does not state
the arbitrary-jet theorem.

The Taylor coefficient-tail estimate and the full remainder bound in terms
of the original degree-d coefficient norm are repository deductions. They
are not attributed verbatim to this paper. In particular, the bound uniform
over all m at least d is not an assertion of the paper's function-norm
approximation theorem alone.

## Verified locator

- DOI: 10.1007/s00365-010-9108-5.
- URL: https://arxiv.org/abs/0808.1936v3.
- Full text: https://arxiv.org/pdf/0808.1936v3.
- Published in *Constructive Approximation* 33, 331--363 (2011).
- arXiv v3, Section 4: equations (27)--(29), Lemma 14, Corollary 16;
  Section 5: Lemmas 23--24.
