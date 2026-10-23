---
bibkey: zhangzhao2024speyer
authors: Rong Zhang, James Jing Yu Zhao
year: 2024
title: Analytic properties of Speyer’s g-polynomial of uniform matroids
doi: 10.1007/s10114-026-4502-5
url: https://arxiv.org/abs/2408.15506v1
claim: Proposition 1.1 gives the uniform-matroid polynomial; Theorem 4.2 gives its normality criterion; Conjecture 4.8 asks for central and local normal limits when rank diverges.
strata_touched:
  - D5/S3/Analytic/Probability/BernoulliTriangularLimits
  - D5/S3/Combinatorics/Matroids/SpeyerUniformNormality
license: citation-only
triage: anchor
---

# Analytic properties of Speyer’s g-polynomial of uniform matroids

## Verified locator

DOI: 10.1007/s10114-026-4502-5

Source: https://arxiv.org/abs/2408.15506v1

## Source statements

Proposition 1.1, page 1:

> For any n ≥ 2 and 1 ≤ d ≤ n − 1, the g-polynomial of the uniform matroid Uₙ,ᵈ is given by
> $g_{U_{n,d}}(t)=\sum_{i=1}^{\min(d,n-d)} \frac{(n-i-1)!}{(d-i)!(n-d-i)!(i-1)!}\, t^i$.

Theorem 4.2, page 9, attributes the criterion to Bender's Theorem 2:

> If $\sigma_n^2\rightarrow +\infty$ as $n \rightarrow +\infty$, then the coefficient of $f_n(t)$ is asymptotically normal with mean $\mu_n$ and variance $\sigma_n^2$ by local and central limit theorems.

Conjecture 4.8, page 13:

> If d = d(n) is a real function of n such that d(n) → +∞ as n → +∞, then the coefficient of Speyer’s g-polynomial gₙ,ᵈ₍ₙ₎(t), namely Sᵢ(n,d(n)), is asymptotically normal by local and central limit theorems.

## Encoding and scope

Rank is integer-valued, and the standing half-rank restriction is required eventually.
The polynomial is the literal factorial sum of Proposition 1.1. The derivative ratios
are the mean and variance of Theorem 4.2. The epsilon-form limits quantify uniformly
over every real threshold. Negative integer coefficient indices have probability zero.
The existing Mathlib owners `gaussianPDFReal 0 1` and `cdf (gaussianReal 0 1)` are
respectively the source's standard Gaussian density and its integral over `Set.Iic`.

The source proves the balanced half-rank case in Theorem 4.1 and ends with
Conjecture 4.8. It makes no bounded-rank claim in that conjecture.

## Literature boundary

The journal version is Acta Mathematica Sinica, English Series 42, 1087–1098.
Its full text remains ASSUMED-UNVERIFIED; the arXiv v1 statement is the verified target.
