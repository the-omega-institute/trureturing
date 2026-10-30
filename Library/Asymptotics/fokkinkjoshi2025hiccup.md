---
bibkey: fokkinkjoshi2025hiccup
authors: Robbert Fokkink, Gandhar Joshi
year: 2025
title: On Cloitre's hiccup sequences
doi: 10.1007/s11139-025-01305-1
url: https://arxiv.org/abs/2507.16956v4
claim: Section 4 generalizes Conjecture 20 to two-parameter continued-fraction tails and their asymptotic Beatty sequence; Theorem 24 proves one parameter case.
strata_touched:
  - D5/S1/Recurrence/ContinuedFractionTailBeattyRefutation
license: citation-only
triage: anchor
---

# On Cloitre's hiccup sequences

## Verified locator

DOI: 10.1007/s11139-025-01305-1

Source: https://arxiv.org/abs/2507.16956v4

The journal version is The Ramanujan Journal 69, article 40 (2026).

## Source statements

Section 4, page 19, after Equation (14):

> We extend the one-parameter family in Equation 11 to the two-parameter family
> $u+v+\mathop{\mathrm K}_{j=1}^{\infty}\frac{j^2}{(j+1)u+v}$, (14)
> for constants u and v. Its tails satisfy $s_n=nu+v+\frac{n^2}{s_{n+1}}$.

> If we assume that $s_n$ converges to $\alpha n+\beta$ with order $O(1/n)$,
> and if we take u to be a natural number, then $\alpha$ is the u-th metallic mean and
> $\beta=\frac{v\alpha^2-\alpha}{\alpha^2+1}$.

> The generalization of Conjecture 20 then says that the rounded down tails of the continued
> fraction give the Beatty sequence with slope $\alpha$ and offset $\beta$.

## Encoding and mathematical boundary

The slope is $(u+\sqrt{u^2+4})/2$, already defined by
`D5.S0.Asymptotics.MetallicFamily.metallicValue`. The offset is real-valued.
Positive tails satisfy the recurrence at every natural index at least one;
the value at zero is unrestricted. The order assumption is a uniform bound
by one real constant divided by the index. Floors are integer-valued.

The refutation uses $u=2$, $v=1$ and index one. A contraction constructs a
positive tail sequence with strictly positive error of order $1/n$.
The universal Pell-index conclusion, uniqueness of positive tails and
identification with limits of finite truncations are outside the formal result.
Conjecture 20 itself has $v=-1$ and is not refuted by this specialization.
Theorem 24 concerns $u=1$, $v=\varphi-1$, so its parameter case is unchanged.

## Literature boundary

The arXiv v4 statement is the target. Completeness of the prior-resolution
screen and the full journal text remain ASSUMED-UNVERIFIED.
