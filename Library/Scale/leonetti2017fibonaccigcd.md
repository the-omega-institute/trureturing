---
bibkey: leonetti2017fibonaccigcd
authors: Paolo Leonetti and Carlo Sanna
year: 2017
title: On the greatest common divisor of n and the nth Fibonacci number
doi: null
url: https://arxiv.org/pdf/1704.00151v2
claim: Lemma 2.4 bounds a weighted Fibonacci entry-point tail; Lemma 2.2(v) identifies the prime lcm outside the exceptional prime five.
strata_touched: []
license: citation-only
triage: anchor
---

# A published weighted entry-point tail

The inspected source is [arXiv:1704.00151v2](https://arxiv.org/pdf/1704.00151v2),
pages 3–4. Write `z(p)` for the Fibonacci entry point and
`ell(p) = lcm(p,z(p))`. Lemma 2.4 states

$$
\sum_{p>y}\frac1{\varphi(\ell(p))}\ll y^{-1/4},\qquad y>0.
$$

Lemma 2.2(v) gives `ell(p) = p z(p)` for primes other than five. Since
`phi(k) <= k`, these two results imply

$$
\sum_{p>y}\frac1{p z(p)}\ll y^{-1/4},\qquad y\ge5.
$$

This is a sufficient published input for the density-one argument in FIB
§192. At cutoff `y = j^(5/6)`, it gives an exceptional-index count
`O_v(X^(19/24) (log X)^2)` after the stated averaging and threshold argument.
The fixed seed and the allowed multiplier constant remain fixed throughout
that limit. The argument does not remove all exceptional indices.

FIB §191 separately records the elementary bucket estimate
`sum_(p>y) 1/(p z(p)) <= 16/sqrt(y)`. Its resulting exponent `7/12`, the
uniform variable-multiplier Robin estimate and the canonical-source
interpretation are project paper deductions, not claims attributed to this
article. No novelty or Lean certification is asserted for those deductions.
