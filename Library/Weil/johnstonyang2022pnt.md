---
bibkey: johnstonyang2022pnt
authors: Daniel R. Johnston and Andrew Yang
year: 2022
title: Some explicit estimates for the error term in the prime number theorem
doi: null
url: https://arxiv.org/abs/2204.01980v2
claim: The unconditional cumulative Chebyshev error bound includes all prime powers. Its weighted fixed-row application controls a signed discrepancy tail, without providing an all-test Weil lower bound.
strata_touched: []
license: citation-only
triage: anchor
---

# A cumulative error supplier for fixed arithmetic rows

The inspected primary version is
[arXiv:2204.01980v2](https://arxiv.org/pdf/2204.01980v2), revised
20 April 2022, 22 pages; its title page is dated 21 April 2022.
PDF SHA-256:
`565993a6def48b237a68a92acba604f2c42f99165e0e71e390f8e21a313b74b2`.
Locators refer to this manuscript; a journal edition is not claimed inspected.

Theorem 1.1, equation (1.3), printed p.2, proves for every $X\ge2$

$$
|\Psi(X)-X|\le
9.39X(\log X)^{1.515}
\exp\bigl(-0.8274\sqrt{\log X}\bigr),
\qquad \Psi(X)=\sum_{n\le X}\Lambda(n).
$$

The sum includes all prime powers. The theorem uses explicit zero-free
and zero-density estimates together with finite verified-zero inputs;
it does not assume global RH. The separate theta and prime-counting
corollaries are not substituted for this Chebyshev estimate.

For $E(t)=\Psi(e^t)-e^t$ the exact parameter map is

$$
|E(t)|\le e^t\epsilon(t),\qquad
\epsilon(t)=9.39t^{1.515}e^{-0.8274\sqrt t},
\quad t\ge\log2.
$$

The [signed-discrepancy application](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/theta-mixed-matrix/signed-discrepancy-window.md)
retains the endpoint in Stieltjes integration and places its derivative
on a specified compact low row. The original theta weight then gives
a tail allowance uniform in the complement's support radius. Those
row and metric deductions are project applications of this bound and
the existing theta supplier, not additional theorems attributed to
Johnston–Yang.

The [existing Trudgian application](trudgian2014pnt.md) controls a
different prime diagonal, while the [complete prime-graph suppliers](lenz2010compactness.md)
already retain both directions and all long edges. No numerical
superiority to those operators is asserted. A cumulative absolute
error estimate by itself supplies neither the required signed all-test
comparison nor RH or Robin positivity.
