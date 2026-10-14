---
bibkey: harm2026shortprogressions
authors: Michael Harm
year: 2026
title: Refinements for primes in short arithmetic progressions
doi: null
url: https://arxiv.org/abs/2507.15334v2
claim: Theorems 2.4 and 2.11 refine pointwise and mean-square short-increment estimates under the stated zero-free and zero-density inputs; they do not control the baseline-containing forward Chebyshev primitive in the selected Robin account.
strata_touched: []
license: citation-only
triage: anchor
---

# Short-increment refinements and the retained Robin baseline

The inspected primary is [arXiv:2507.15334v2](https://arxiv.org/html/2507.15334v2),
19 May 2026, *Refinements for primes in short arithmetic progressions*.
Theorem 2.4 is a pointwise estimate for the short-interval prime-count
error $\Delta_\pi(x,y,q,a)$. Theorem 2.11 is its mean-square counterpart
over real centers $X\le u\le2X$, summed over reduced residues modulo
$q$. Both assume Conditions 1.1 and 1.2, with the stated restriction
on the zero-free-region parameter and density exponent. Their
interval-length ranges, zero-free factors and logarithmic losses
must all be retained. These are `literature-attested` inputs; neither
analytic proof is reproduced or Lean verified here.

For the ordinary prime problem take modulus $q=1$ and residue $a=1$.
The paper explicitly allows density exponent $A=30/13$ in that case
from Guth--Maynard. This letter $A$ and the paper's zero-free function
$\eta$ are separate from the Robin source's total clock $A=B+t$ and
source exponent $\eta$. Section 3.1 defines $\Delta_\pi$,
$\Delta_\vartheta$ and $\Delta_\psi$ and their conversion errors;
the theorem for $\Delta_\pi$ must not be silently substituted for a
complete-$\psi$ theorem.

In the [forward-primitive consumer PE3--PE7](../Estimation/trureturing2026pricegapconvexity.md#retain-the-compensation-while-controlling-forward-primitive-excursions),
the relevant ordinary center is the same actual real center after
any required change of variables. Its observable includes
$(v-u)E(u)$ in addition to the integrated short-increment error,
where $E(u)=u-\psi(u)$. The source's $E(A)=t+Q(A)$ is endogenous.
The cited increment theorems do not provide an estimate for that
baseline, the complete future primitive, its amplitude-integrated
exceptional occupation, or the original signed growing head.
No fixed-tolerance or density-one conclusion from this paper is
asserted to close the selected Robin comparison or prove RH.
