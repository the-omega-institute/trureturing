---
bibkey: danesh2026ramanujanrobin
authors: Payam Danesh
year: 2026
title: A Ramanujan view of Robin's inequality
doi: 10.33774/coe-2026-5cw2z
url: https://doi.org/10.33774/coe-2026-5cw2z
claim: The working paper derives Ramanujan/Lambert-series identities for a smoothed Robin defect and explicitly identifies coefficientwise positivity at divisor-rich integers as the missing step; it supplies no pointwise estimate for a FIB source.
strata_touched: []
license: citation-only
triage: anchor
---

# A Ramanujan view of Robin's inequality

The source is Payam Danesh, Cambridge Open Engage working paper, DOI
[10.33774/coe-2026-5cw2z](https://doi.org/10.33774/coe-2026-5cw2z), published 9 July 2026. It is not peer reviewed and was not formalized here.

## Exact analytic interface

For

$$
S(x)=\sum_{n\ge1}\sigma(n)e^{-nx},
$$

the paper records the Lambert-series identity

$$
S(x)=\sum_{m\ge1}\frac{m}{e^{mx}-1},
$$

and its Mellin transform

$$
\int_0^\infty S(x)x^{s-1}\,dx
=\Gamma(s)\zeta(s)\zeta(s-1)
$$

in the absolute-convergence half-plane. Its Ramanujan transformation rewrites the same smoothed series in a dual scale. The paper uses this to express a Laplace transform of the Robin defect and to separate smoothed positivity from coefficientwise positivity.

The paper's conclusion is deliberately limited: a positive transformed or smoothed quantity does not imply

$$
e^\gamma n\log\log n-\sigma(n)>0
$$

for every individual integer. Any possible failure remains concentrated on divisor-rich extremal integers such as CA or highest abundant numbers.

## Boundary for FIB

The transform acts on the complete sequence $\sigma(n)$ and its Laplace/Mellin averages. A five-window FIB address gives an additive Zeckendorf inclusion path; it does not supply a coefficientwise lower bound for the defect at the associated integer, nor does it identify that integer as CA or highest abundant. Smoothing the FIB family and proving positivity of the smoothed image would therefore leave the same pointwise gap as §250's signed $\Phi$ term. This source is a diagnostic for the existing gap, not a new Robin estimate or an RH proof.
