---
bibkey: hanaoka2021rieszwalk
authors: Ryota Hanaoka, Norio Konno
year: 2021
title: "Return probability and self-similarity of the Riesz walk"
doi: 10.26421/QIC21.5-6-5
url: https://arxiv.org/abs/2010.04518v3
claim: "Section 2 defines the Riesz walk; Conjecture 4.2 states equality of its probabilities in the same rescaled intervals at times 2t and 8t."
strata_touched:
  - D5/S3/Quantum/Walks/RieszWalkSelfSimilarity
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.26421/QIC21.5-6-5

Source: https://arxiv.org/abs/2010.04518v3

Paper: https://arxiv.org/abs/2010.04518

## Conjecture 4.2

Section 4, arXiv PDF p. 12, states:

> Let $\mathbb Z_{>}=\{1,2,3,\ldots\}$. For each $n\in\mathbb Z_{>}$, we put $T_0(n)=\{0\}$, and $T_k(n)=((k-1)/n,k/n]$ $(1\leq k\leq n)$. Then, for the measure of the Riesz walk with initial state of $\Psi_0=[1,0]^{\mathrm T}\delta_0$,
> $$P\left(\frac{X_{2t}}{2t}\in T_k(t)\right)=P\left(\frac{X_{8t}}{8t}\in T_k(t)\right),$$
> for any $t\in\mathbb Z_{>}$.

The index includes the singleton block $k=0$ and all $1\le k\le t$.
The real-valued moment form gives the paper's walk because its moments are real.
Site $x$ has coordinates $2x$ and $2x+1$. The probabilities use rational interval
endpoints and a real sum over the sites.

## Definitions in Section 2

The following sentences are quoted from arXiv PDF p. 2:

> Given a measure μ on ∂D, the Carathéodory and Schur functions are defined as follows.

> Then, the Verblunsky parameters αₖ are given by the following algorithm.

> where f₀(z) = f(z).

> From the Verblunsky parameters, the corresponding QW on ℤ≥ is determined by

> The evolution is defined by the equation Ψₜ₊₁ = U⁽ˢ⁾Ψₜ, where Ψₜ = [Ψₜ(0), Ψₜ(1), Ψₜ(2), …]ᵀ.

> Then the probability of location x at time t is given by μₜ(x)=‖Ψₜ(x)‖²=|Ψₜᴸ(x)|²+|Ψₜᴿ(x)|².

PDF p. 3 introduces the product with:

> The Riesz measure on the unit circle ∂D in ℂ is defined by

$$d\mu(z)=\prod_{k=1}^{\infty}\left(1+\frac{z^{4^k}+z^{-4^k}}{2}\right)\frac{dz}{2\pi iz}.$$

The formal series uses the real stabilized coefficients of this product. The
Schur recursion, the site blocks and the walk's initial amplitude use these
coefficients; the two components at site $x$ are indexed by $2x$ and $2x+1$.

PDF p. 8 states:

> Laurent polynomials {χⱼ}ⱼ₌₀∞ are obtained from the Gram-Schmidt orthonormalization of {1,z,z⁻¹,z²,z⁻²,…}.

## Formal power-series Schur functions

The expressions $z^{-1}(F-1)/(F+1)$ and
$z^{-1}(f-f(0))/(1-f(0)f)$ remove a vanishing constant coefficient.
In Mathlib, $X^{-1}=0$ in the power-series ring. Removing this monomial therefore
means shifting coefficients after multiplying by the inverse of the unit denominator.
The identities $Xf(F+1)=F-1$ and
$Xf_{k+1}(1-f_k(0)f_k)=f_k-f_k(0)$ express the source's equations.
The finite positive Gram form ensures $1-f_k(0)^2>0$.

The neighboring Conjectures 4.1 and 4.3 and the general $m\ge3$ walks are separate questions.
