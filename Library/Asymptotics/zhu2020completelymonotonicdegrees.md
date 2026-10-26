---
bibkey: zhu2020completelymonotonicdegrees
authors: L. Zhu
year: 2020
title: "Completely monotonic integer degrees for a class of special functions"
doi: 10.3934/math.2020224
url: https://www.aimspress.com/article/doi/10.3934/math.2020224
claim: "Conjecture 6.4 asserts positivity at derivative order m+2n-2 and failure of positivity everywhere at order m+2n-1 for the signed Bernoulli remainder, for integers m >= 1 and n >= 2."
strata_touched:
  - D5/S3/Analytic/CothBernoulliDegree/Defs
  - D5/S3/Analytic/CothBernoulliDegree/Result
license: citation-only
triage: anchor
---

# Completely monotonic integer degrees of a hyperbolic cotangent remainder

## Verified locator

L. Zhu, *Completely monotonic integer degrees for a class of special functions*,
**AIMS Mathematics** 5(4) (2020), 3456–3471.

DOI: 10.3934/math.2020224

Source: https://www.aimspress.com/article/doi/10.3934/math.2020224

Conjecture 6.4, equations (6.12) and (6.13), uses the remainder defined in
equation (2.2).

## Mathematical correspondence

Equation (2.2) defines

$$p_n(t)=\frac{\coth t}{t}
-\sum_{k=0}^{n}\frac{2^{2k}B_{2k}}{(2k)!}t^{2k-2}.$$

For integers $m\ge1$, $n\ge2$, put $M=m+2n$ and
$P(t)=(-1)^nt^mp_n(t)$. Conjecture 6.4 states that $P^{(M-2)}(t)>0$
for every $t>0$, while $P^{(M-1)}(t)>0$ does not hold for every $t>0$.
The two clauses are equations (6.12) and (6.13).

`Defs.p`, `Defs.P` and `Defs.claim` in
`D5/S3/Analytic/CothBernoulliDegree/Defs` retain these definitions and
quantifiers. Integer powers are used in the finite remainder sum, including
$t^{-2}$ at $k=0$. Only even Bernoulli indices occur, so the convention for
$B_1$ does not affect the remainder.
`D5/S3/Analytic/CothBernoulliDegree/Result.result` proves both clauses.

The bounded literature scope and its limitations are stated in
`Problems/zhu-2020-coth-bernoulli-remainder-derivative-signs.md`.
