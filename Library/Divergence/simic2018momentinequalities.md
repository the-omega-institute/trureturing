---
bibkey: simic2018momentinequalities
authors: S. Simić
year: 2018
title: Second and third order moment inequalities for probability distributions
doi: 10.1007/s10474-018-0848-1
url: https://arxiv.org/abs/1509.08519v2
claim: "Conjectures 1 and 2 are the eight-parameter and displaced-parameter iterated moment minor inequalities."
strata_touched:
  - D5/S3/Analytic/MomentMinors/Defs
  - D5/S3/Analytic/MomentMinors/MomentKernel
  - D5/S3/Analytic/MomentMinors/PairMinor
  - D5/S3/Analytic/MomentMinors/Result
license: citation-only
triage: anchor
---

# Second and third order moment inequalities for probability distributions

## Verified locator

DOI: https://doi.org/10.1007/s10474-018-0848-1

Source: https://arxiv.org/abs/1509.08519v2

Acta Mathematica Hungarica 155 (2018), 518–532. The arXiv title is
*Moment inequalities of the second and third order*.
Section 1 defines the normalized moment gap λ_s and its second minor ξ.
Theorem 3 proves φ ≥ 0. Section 2 states Conjecture 1, the eight-parameter
refinement involving two φ values, and Conjecture 2, the displaced-parameter
inequality involving θ_a. The source assumes moments exist for every
parameter in the interval I. The logarithmic limiting cases require the
corresponding logarithmic moments.

The Lean definitions retain the probability-law, positivity and integrability
conditions, including the two logarithmic cases. The settling theorem
`D5/S3/Analytic/MomentMinors/Result.result` proves both inequalities by
positive semidefiniteness of the midpoint moment kernel and successive
second-minor constructions.
