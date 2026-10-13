---
bibkey: farkas2021alternating
authors: Gavril Farkas; Riccardo Moschetti; Juan Carlos Naranjo; Gian Pietro Pirola
year: 2021
title: Alternating Catalan numbers and curves with triple ramification
doi: 10.2422/2036-2145.201909_009
url: https://arxiv.org/abs/1906.10406
claim: Theorem 1.1 expresses the number of minimal odd covers of a general curve as a signed binomial sum of Catalan numbers.
strata_touched:
  - D5/S1/Recurrence/A308815DFiniteRecurrence
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.2422/2036-2145.201909_009

Source: https://arxiv.org/abs/1906.10406

Theorem 1.1 on page 1 of arXiv:1906.10406v2 says:

> The number of odd covers of degree 2g + 1 of a general curve of genus g ≥ 3 equals

Its displayed expression is

$$A_g=16^g\sum_{i=0}^{g}(-2)^i\binom{g}{i}C_{2g-i}.$$

The introduction defines `C_n` as the ordinary Catalan number. The Lean
sequence `a308815` uses Mathlib's natural-valued `catalan`, coerces each summand
to the integers and denotes the genus by `n`. The sum also defines the sequence
at `n = 0, 1, 2`; the odd-cover interpretation in Theorem 1.1 starts at `g ≥ 3`.
The geometric counting theorem is cited, not formalized by the recurrence
module.

Theorem 1.2 on page 1 supplies an algebraic generating function. Mathar's
order-three recurrence in OEIS A308815 is a separate assertion. The recurrence
proof uses the quadratic identity of the ordinary Catalan series and a
coefficient certificate; it does not formalize the paper's generating-function
formula or the OEIS asymptotic formula.
