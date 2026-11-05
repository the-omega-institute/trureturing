---
bibkey: lanier2025maximal
authors: D. Lanier; J. Béguinot; O. Rioul
year: 2025
title: "From Classical to Quantum: Explicit Classical Distributions Achieving Maximal Quantum f-Divergence"
doi: 10.48550/arXiv.2501.14340
url: https://arxiv.org/abs/2501.14340v1
claim: "We conjecture that (49) is in fact not necessary for (50) to hold."
strata_touched:
  - D5/S3/Divergence/LanierBeguinotRioulReversePinskerRefutation
license: citation-only
triage: anchor
---

# From Classical to Quantum: Explicit Classical Distributions Achieving Maximal Quantum f-Divergence

D. Lanier, J. Béguinot and O. Rioul, arXiv:2501.14340v1.

## Verified locator

DOI: 10.48550/arXiv.2501.14340

Source: https://arxiv.org/abs/2501.14340v1

## Statement and scope

Section I, p. 1:

> Let f(x) be a convex, real-valued function defined for x ≥ 0 and satisfying f(1) = 0.

Theorem 1, equation (4), defines the maximal spectral expression

$$
D_f^{\max}(\rho\Vert\sigma)
=\operatorname{Tr}\bigl(\sigma^{1/2}
 f(\sigma^{-1/2}\rho\sigma^{-1/2})\sigma^{1/2}\bigr).
$$

Theorem 4, p. 4, assumes condition (49), $|\rho-\sigma|\leq\rho+\sigma$,
and asserts equation (50):

$$
D_f(\rho\Vert\sigma)\leq\frac{\|\rho-\sigma\|_1}{2}
\left(\frac{f(m)}{1-m}+\frac{f(M)}{M-1}\right),
$$

where $m,M$ are the smallest and largest eigenvalues of
$\sigma^{-1/2}\rho\sigma^{-1/2}$.

Section III-C, p. 5:

> Our bound holds in general for any f-divergence, in particular for the maximal f-divergence.

> We conjecture that (49) is in fact not necessary for (50) to hold.

The qubit matrices $\sigma=\operatorname{diag}(9/25,16/25)$ and
$\rho=((9/25,12/125),(12/125,16/25))$, with $f(x)=(x-1)^2$, give
$D_f^{\max}=25/625$ and a right-hand side of $24/625$.
They also satisfy (49), so the failure concerns the printed conditional maximal-divergence inequality.
These statements use the spectral expression (4). Its status as a quantum
f-divergence of Definition 2 for an operator-convex generator uses the
Matsumoto theorem cited by the source; that general data-processing theorem
is not separately formalized here. Global prior-art completeness remains
`ASSUMED-UNVERIFIED`.
