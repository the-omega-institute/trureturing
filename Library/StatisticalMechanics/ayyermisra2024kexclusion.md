---
bibkey: ayyermisra2024kexclusion
authors: Arvind Ayyer and Samarth Misra
year: 2024
title: An exactly solvable asymmetric K-exclusion process
doi: 10.1088/1751-8121/ad5edd
url: https://arxiv.org/abs/2310.03343v2
claim: "Section 4.5 asks which adjacent occupation is most likely at half-integer density for small and large positive t."
strata_touched:
  - D5/S3/Combinatorics/Probability/AyyerMisraHalfDensityMode
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1088/1751-8121/ad5edd

Source: https://arxiv.org/abs/2310.03343v2

The journal reference is *Journal of Physics A: Mathematical and Theoretical*
57, 315001. The quotations and page numbers below refer to arXiv version 2.

# Half-density site occupation

Section 4.5, page 21:

> We focus on when t ≪ 1 and t ≫ 1. From the discussion in Sections 4.2
> and 4.3, we know that the most likely number of particles is either k or k + 1.
> The question we want to address is which one is most likely.

Page 22:

> We now claim that, for L > 2,
> 1. the top (and bottom) k + 1 coefficients of these polynomials are equal,
> 2. the (k + 2)’th coefficient for π(η₁ = k) is larger (resp. smaller) if
> n < KL/2 (resp. n > KL/2), and
> 3. both are equal polynomials if n = KL/2.

Page 4: “We define the t-analog of a nonnegative integer k as”.
Equation (4) is $[k] \equiv [k]_t = \sum_{i=0}^{k-1}t^i$.
Page 6: “The t-analogue of the factorial is given by”. Equation (8) is
$[k]! \equiv [k]_t! = [1][2]\cdots[k]$.
“The t-binomial coefficient or Gaussian polynomial is”. Equation (9) is
${k\brack i} \equiv {k\brack i}_t = [k]!/([k-i]![i]!)$.

Page 4:

> We denote the set of configurations by

Equation (1) is $\Omega_{L,n}\equiv\Omega^K_{L,n}
=\{\eta\in\{0,1,\ldots,K\}^L\mid\sum_{i=1}^L\eta_i=n\}$.

Page 6:

> We will show in Section 3 that the steady state weight is given by the formula,

Equation (11) is
$\operatorname{wt}_{\eta}(t)=\prod_{i=1}^{L}
t^{(\eta_i-1)(\eta_i-2)/2}{K\brack\eta_i}_t$.
“Then the steady state probability of η is”. Equation (13) is
$\pi(\eta)=\operatorname{wt}_{\eta}(t)/Z_{L,n}(t)$.

For a natural occupation a, the Lean exponent is
`Nat.div (a*a+2-3*a) 2`, with natural subtraction. Its first five values are
1, 0, 0, 1, 3. Configurations are functions `Fin L → Fin (K+1)` whose
natural values sum to n. The site marginal divides the sum of weights
with the selected occupation by the sum over all configurations.

The accompanying theorem answers the mode question for L = 2r ≥ 4,
n = (2k+1)r and k < K. In the two parameter extremes the unique mode is
k below half filling and k+1 above it. At exact half filling the two
occupations tie, and exceed every other occupation in those regimes.
The theorem makes no classification for intermediate positive t.

The high-density coefficient index in the source requires correction:
the first difference has offset K−k above the lowest degree, rather than
k+1. This correction does not change the mode question or constitute a
second settlement.

The exact-polynomial experiment is in
`the-omega-institute/trureturing-experiments`,
`docs/reports/ayyer-misra-2024-kasep-half-density-mode/`, commit
`65de77d642c949fc7345e8925672d34307a37483`. Its `check.py` SHA-256 is
`981cb87280b7803982fff61a939dc741b7cd3a1513311c7e9bfec4785ddebf9e`;
The exact script checks 84 parameter triples and exits 0. The theorem
uses no experimental premise.

The literature screen in issue #18570 includes the source, citing papers
and later papers of the authors. Completeness is `ASSUMED-UNVERIFIED`.
