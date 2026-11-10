---
bibkey: kittanehkosaki1987powers
authors: Fuad Kittaneh; Hideki Kosaki
year: 1987
title: Inequalities for the Schatten p-norm V
doi: 10.2977/PRIMS/1195176547
url: https://ems.press/journals/prims/articles/3346
claim: Positive bounded operators satisfy the operator-norm continuity bound for operator-monotone functions continuous at zero and vanishing there, including fractional powers with exponent between zero and one.
strata_touched:
  - D5/S3/Quantum/Analysis/FractionalPowerHolder
license: citation-only
triage: anchor
---

# Fractional-power operator-norm continuity

## Verified locator

DOI: https://doi.org/10.2977/PRIMS/1195176547

Publisher: https://ems.press/journals/prims/articles/3346

Public article: https://ems.press/content/serial-article-files/42385?nt=1

Theorem 2.3, pp. 436–438, in Publications of the Research Institute for
Mathematical Sciences 23 (1987), no. 2, 433–443. The publisher and Crossref
record the publication date as 30 April 1987.

## Scope and attribution

The theorem states that for positive bounded operators A and B on a Hilbert
space and an operator-monotone function f continuous at zero with f(0)=0,
the operator norm of f(A)-f(B) is at most f(norm(A-B)). The discussion before
the theorem explicitly includes fractional powers with exponents in (0,1).
The proof uses scalar shifts, operator monotonicity and the commutative
functional calculus. The source is a classical mathematical precedent,
not Lean code reused here.

The Lean result proves the fractional-power estimate in an arbitrary ordered
unital complex C-star algebra, including the trivial algebra, from Mathlib's
operator-monotone power function, continuous functional calculus, scalar
subadditivity and self-adjoint norm-order bounds. Its trace-class compression
application uses the existing project trace-norm estimate and the norm bound
for inclusion into bounded operators. No literature novelty is claimed.
