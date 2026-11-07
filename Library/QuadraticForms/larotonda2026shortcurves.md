---
bibkey: larotonda2026shortcurves
authors: Gabriel Larotonda
year: 2026
title: "Short curves in homogeneous spaces of the unitary group for unitarily invariant norms"
doi: 10.48550/arXiv.2610.31535
url: https://arxiv.org/abs/2610.31535v1
claim: "The unnumbered conjecture after Proposition 4.3 asserts principal-log minimality for all normalized Ad-invariant Finsler norms on u(n)."
strata_touched:
  - D5/S3/QuadraticForms/LarotondaPrincipalLogDistanceRefutation
license: citation-only
triage: anchor
---

# Short curves in homogeneous spaces of the unitary group

## Verified locator

DOI: 10.48550/arXiv.2610.31535

Source: https://arxiv.org/abs/2610.31535v1

Primary text: https://arxiv.org/pdf/2610.31535v1, p. 7, final paragraph of Section 4.1 after Proposition 4.3.

## Source statement

The TeX sentence is:

```tex
It would be natural to conjecture that $d(1,e^z)=\nn{z}$ whenever $\nn{z}_\infty\le\pi$.
```

The source macro `\nn{x}` means $\|x\|$. Thus the printed sentence reads:

> It would be natural to conjecture that $d(1,e^z)=\|z\|$ whenever $\|z\|_\infty\le\pi$.

Section 2.1, p. 2:

> The length of a piecewise smooth curve $\gamma\subset\mathrm U(n)$ is $L(\gamma)=\int\|\gamma^{-1}\dot\gamma\|$, and $d$ is the induced rectifiable distance, which is bi-invariant.

Section 4, p. 5:

> Let $\|\cdot\|$ be an $\mathrm{Ad}$-invariant Finsler norm on $\mathfrak{su}(n)$, that is, a subadditive, nondegenerate and positively homogeneous function ($\|\lambda v\|=\lambda\|v\|$ for $\lambda\ge0$) with $\|\mathrm{Ad}_uv\|=\|v\|$ for $u\in\mathrm{SU}(n)$; we do not assume $\|-v\|=\|v\|$.

> Throughout, $d(u,w)$ is the distance *from* $u$ *to* $w$: the infimum of $L(\gamma)=\int\|\gamma^{-1}\dot\gamma\|$ over curves $\gamma$ starting at $u$ and ending at $w$.

Section 4.1, p. 7 applies the Finsler definition to $\mathfrak u(n)$. The conjecture on p. 7 assumes $\|x\|_\infty\le\|x\|$. It adds neither symmetry nor trace zero nor the stronger singular-value invariance used in Theorem 1.1.

## Mathematical scope

The refutation uses a symmetric Ad-invariant norm with a trace coupling, in dimension two. A winding shift preserves the exponential and gives a shorter smooth curve. It does not compute the exact global distance. Proposition 4.3 and the established quotient theorem for the stronger unitarily invariant class are not refuted.
