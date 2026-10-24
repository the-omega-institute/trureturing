---
bibkey: grunwaldpales2024gini
authors: R. Grünwald; Zs. Páles
year: 2024
title: "Comparison of Gini means with fixed number of variables"
doi: null
url: https://arxiv.org/abs/2408.07658v1
claim: "Section 4, Conjecture 1 proposes that the parameter-sum inequality and two extreme endpoint tests characterize comparison of Gini means on a bounded positive interval for n ≥ 3."
strata_touched:
  - D5/S3/ArithSums/GiniMeanEndpointComparison
license: citation-only
triage: anchor
---

## Locator

Author text: <https://arxiv.org/abs/2408.07658v1>.
Additional locators: §4, Conjecture 2 (the stationary characterization for intervals whose quotient set has infimum zero), and Theorem 7 (the bounded-interval comparison characterization).
R. Grünwald and Zs. Páles, *Comparison of Gini means with fixed number of variables*, arXiv:2408.07658v1, §4, introductory paragraph and Conjecture 1. The journal bibliographic reference is *Results in Mathematics* 80 (2025), article 54. The journal version's text is ASSUMED-UNVERIFIED; the quotations and locators bind to the arXiv version.

## Endpoint characterization

The introductory paragraph states verbatim:

> We conclude this paper by formulating two conjectures that we have not been able to verify. The first conjecture seems to be a natural extension of the formula for Γ2(I), if 0 < inf I < sup I < ∞.

Conjecture 1 states verbatim:

> Conjecture 1. Let n ≥ 3 and let I be a subinterval of R+ such that 0 < a := inf I < sup I =: b < ∞. Then Γn(I) = {((r, s), (p, q)) ∈ R² × R² | r + s ≤ p + q, G[n]r,s(a, …, a, b) ≤ G[n]p,q(a, …, a, b), and G[n]r,s(a, b, …, b) ≤ G[n]p,q(a, b, …, b)}.

Here $\Gamma_n(I)$ consists of parameter pairs for which $G_{r,s}(x)\le G_{p,q}(x)$ for every $x\in I^n$. For distinct parameters and positive coordinates,

$$
G_{r,s}(x)=\left(\frac{\sum_{i=1}^n x_i^r}{\sum_{i=1}^n x_i^s}\right)^{1/(r-s)}.
$$

## Repository-derived refutation

The theorem `D5.S3.ArithSums.GiniMeanEndpointComparison.result : ¬ claim` refutes the proposed $\supseteq$ inclusion, restricted to distinct parameters and closed intervals. The witness is $n=3$, $I=[1,3]$, $(r,s)=(3,-1)$ and $(p,q)=(0,2)$. The parameter sums are both 2. At $(1,1,3)$ the fourth powers are $87/7<121/9$, and at $(1,3,3)$ they are $33<361/9$. At $x=(1,1,5/3)$ they are $895/351>1849/729$, since $895\cdot729=652455>648999=1849\cdot351$.

Homogeneity identifies this interior tuple with an endpoint configuration for a smaller ratio, $5/3$ rather than 3. The comparison can fail at the smaller ratio while holding at the larger ratio. Requiring both endpoint tests at every ratio $t\in(1,b/a]$ is a candidate correction whose sufficiency is not proved. Conjecture 2, concerning intervals with $\inf I=0$ or $\sup I=\infty$, and the true bounded-interval description of $\Gamma_n(I)$ are not settled by this result.
