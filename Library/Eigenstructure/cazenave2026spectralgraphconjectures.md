---
bibkey: cazenave2026spectralgraphconjectures
authors: Tristan Cazenave
year: 2026
title: Lemmas and Conjectures in Spectral Graph Theory
doi: null
url: https://arxiv.org/abs/2611.03879v1
claim: "Conjectures 4 (#112951) and 5 (#239534): λ₁ ≤ R + µ₂ and µ₂ + rk(A) ≤ 2m for connected simple undirected graphs of order at least two."
strata_touched:
  - D5/S3/Combinatorics/SpectralGraph/CazenaveRandicSpectralBound
  - D5/S3/Combinatorics/SpectralGraph/CazenaveLaplacianRankBound
license: citation-only
triage: anchor
---

# Cazenave's adjacency–Randić–Laplacian inequality

## Verified locator

Source: https://arxiv.org/abs/2611.03879v1

PDF: https://arxiv.org/pdf/2611.03879v1

## Source statement

Page 1, Section 1, states:

> All graphs are simple, undirected and *connected*, with $n\ge 2$ vertices and $m$ edges.

The same page specifies:

> $A$ is the adjacency matrix, with eigenvalues $\lambda_1\ge\lambda_2\ge\dots\ge\lambda_n$ (counted with multiplicity) and rank $\operatorname{rk}(A)$.
>
> $\mathcal{L}=D-A$ is the Laplacian, with eigenvalues $\mu_1\ge\mu_2\ge\dots\ge\mu_n=0$.
>
> $R=\sum_{uv\in E}(d_ud_v)^{-1/2}$ is the Randić index.

Page 11, Section 7, states:

> Conjecture 4 (#112951). $\lambda_1\le R+\mu_2$.
>
> It mixes three spectra: adjacency, Laplacian and Randić. Equality holds for $K_2$.

The adjacency and ordinary Laplacian spectra use decreasing algebraic order,
with multiplicity. The Randić sum counts each unordered edge once.
In the Lean statement, `Fin (n + 2)` ranges over every allowed graph order;
`adjEig G 0` denotes the largest adjacency eigenvalue, and
`LinWangCaiBroomSpectralRatio.lapEig G 1` denotes the second-largest ordinary
Laplacian eigenvalue. The scalar reciprocal square root is evaluated only on
edges, whose endpoint degrees are positive.


## Laplacian–rank conjecture

The same Section 7 states:

> Conjecture 5 (#239534). $\mu_2+\operatorname{rk}(A)\le2m$.

The source TeX gives this statement at main.tex lines 752–754 and the
conventions at lines 48–69. The arXiv v1 source archive has SHA-256
aebb9213f3b0158c9b0dc52155886fcc663a830367bdad713a9133eb52729975.
The Laplacian is the ordinary unnormalized matrix $D-A$. Its eigenvalues
are decreasing, with multiplicity; the rank is real adjacency rank and
$m$ counts unordered edges once. In the corresponding Lean statement,
LinWangCaiBroomSpectralRatio.lapEig G 1 is exactly this second largest
Laplacian eigenvalue, including the smaller eigenvalue at order two.
The parameter Fin (n + 2) covers every order at least two.
