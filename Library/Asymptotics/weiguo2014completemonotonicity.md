---
bibkey: weiguo2014completemonotonicity
authors: C.-F. Wei and B.-N. Guo
year: 2014
title: Complete monotonicity of functions connected with the exponential function and derivatives
doi: 10.1155/2014/851213
url: https://doi.org/10.1155/2014/851213
claim: "Section 5, Conjecture 12 asserts complete monotonicity of both consecutive signed derivative ratios for every nonnegative integer index."
strata_touched:
  - D5/S3/Analytic/ExpRatioCM/Defs
  - D5/S3/Analytic/ExpRatioCM/Result
license: citation-only
triage: anchor
---

# Complete monotonicity of exponential derivative ratios

## Verified locator

DOI: 10.1155/2014/851213

Source: https://doi.org/10.1155/2014/851213

C.-F. Wei and B.-N. Guo, *Complete monotonicity of functions connected
with the exponential function and derivatives*, *Abstract and Applied
Analysis* 2014, Article ID 851213, 5 pp. Section 5, Conjecture 12;
definitions (6) and (10), with the alternative expressions (27).
Equation (30) verifies the indices zero and one.

## Mathematical correspondence

For every nonnegative integer $i$, equation (6) defines

$$F_i(t)=(-1)^i\left(\frac1{e^t-1}\right)^{(i)},\qquad
G_i(t)=(-1)^i\left(\frac1{1-e^{-t}}\right)^{(i)}.$$

Equation (10) defines $\mathcal F_i=F_{i+1}/F_i$ and
$\mathcal G_i=G_{i+1}/G_i$. Conjecture 12 asserts that both ratios
are completely monotonic on $(0,\infty)$ for every such index.

The six definitions in `D5/S3/Analytic/ExpRatioCM/Defs` implement
these functions, their ratios, complete monotonicity and the universal
assertion. Complete monotonicity includes smoothness on the open
positive half-line and nonnegativity of every alternating derivative,
including derivative order zero. Globally defined iterated derivatives
are compared by neighborhood equality at positive arguments.

`D5/S3/Analytic/ExpRatioCM/Result.result` refutes the universal
assertion. `Positive.cm_of_le_two` gives the positive range through index
two, while `Result.not_cm_of_three_le` excludes every index at least
three; `Result.failure_on_every_tail` supplies simultaneous negative
alternating derivatives of both ratios arbitrarily far to the right.

## Literature scope

Guo–Qi, arXiv:2201.06970, Section 5, Proposition 5.1, strengthens the
decreasing property to the range $(1,\infty)$ and does not address
complete monotonicity of the ratios. No settlement was found in the
bounded scope consisting of the title, DOI and conjecture queries,
Proskurnikov–Runvik–Medvedev, arXiv:2302.01364, Appendix B,
Formal Conjectures, conjectures.io, and the corresponding local
mathematical and bibliographic entries. This scope does not establish
exhaustive citation-index coverage or priority. The scope and its
limitations are also stated in
`Problems/wei-guo-2014-exponential-derivative-ratio-complete-monotonicity.md`.
