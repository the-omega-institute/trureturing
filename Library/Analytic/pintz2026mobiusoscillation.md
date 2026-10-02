---
bibkey: pintz2026mobiusoscillation
authors: János Pintz
year: 2026
title: Oscillation of partial sums of the Möbius function and zeros of Riemann's zeta function
doi: null
url: https://arxiv.org/abs/2608.24878v1
claim: The preprint relates the average size of the Möbius summatory function on long initial intervals to the largest error term in the Riemann--von Mangoldt prime formula; this average relation does not provide a pointwise bound on selected FIB integers.
strata_touched: []
license: citation-only
triage: anchor
---

# Möbius oscillation and the pointwise boundary

The source is [arXiv:2608.24878v1](https://arxiv.org/pdf/2608.24878v1), submitted 25 August 2026. This card records the stated relation and its scope; the complete proof was not independently audited here, and no Lean verification is claimed.

The paper studies the summatory Möbius function

$$
M(x)=\sum_{n\le x}\mu(n)
$$

and reports that the average order of $|M(x)|$ over an initial interval agrees, with high accuracy for large endpoints, with the largest error term in the Riemann--von Mangoldt prime-counting formula at the same scale.

## Boundary of the FIB/Robin interface

This is information about an average signed cancellation profile. The FIB Robin obligation is pointwise: one must control the complete signed residual at each actual $N_g=1+F_rg$, with its divisors and prime-power history fixed. An average over $x$ cannot be restricted to that sparse affine family without a transport estimate, and it does not bound the largest residual on the family.

The result is therefore useful as a source for the signed-tail vocabulary, but it does not close the joint estimate in §233.5 or imply Robin's inequality or RH.
