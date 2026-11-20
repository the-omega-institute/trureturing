---
bibkey: mannamandaltura2026spectralcographs
authors: Pallabi Manna and Santanu Mandal and Fernando C. Tura
year: 2026
title: "The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix"
doi: null
url: https://arxiv.org/abs/2611.06981v1
claim: "Open Problem 14.2(ii) asks for a characterization of connected cographs attaining the distance-multiplicity bound and an explicit infinite family attaining it."
strata_touched:
  - D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance
  - D5/S3/Combinatorics/SpectralGraph/Cographs/CographDistanceMultiplicity
license: CC-BY-4.0
triage: anchor
---

# Ordinary distance multiplicity in connected cographs

## Verified locator

- [arXiv:2611.06981v1](https://arxiv.org/abs/2611.06981v1)
- [Theorem 6.4, page 14](https://arxiv.org/pdf/2611.06981v1#page=14)
- [Open Problem 14.2(ii), page 22](https://arxiv.org/pdf/2611.06981v1#page=22)
- [CC BY 4.0 license for this version](https://creativecommons.org/licenses/by/4.0/)

## Source statement

Section 6 uses the ordinary shortest-path distance matrix $D(G)$ and
the Dilworth number $\nabla(G)$, the minimum number of vicinal chains
covering the vertices. Theorem 6.4, attributed to Lou and Lin, bounds
$m_G(\lambda)$ by $\nabla(G)$ at distance eigenvalues
$\lambda\notin\{-1,-2\}$.

Open Problem 14.2(ii) asks to “Characterize the connected cographs for
which $m_G(\lambda)=\nabla(G)$ for some $\lambda\ne -1,-2$, and give
an explicit infinite family attaining the bound of Theorem 6.4.”

## Formal scope

The explicit family is formed by joining a clique of size $r$ to the
disjoint union of $K_{s,s}$ and $b$ isolated vertices. The Lean result
uses ordinary native graph distances, the minimum vicinal chain cover
and the real dimension of the eigenspace at $s-2$. For the real symmetric
distance matrix, this dimension is the spectral multiplicity. The
specialization $r=3(s-1)$, $b=s$, $s\ge2$ has unbounded order and
attains the bound at width two. The cotree characterization treats width
one directly and uses an exact real guard-root criterion at larger widths.

The construction and proof are given in the [analytic result for issue
#32326](https://github.com/the-omega-institute/trureturing/issues/32326#issuecomment-7043985785).
The rank calculation uses the same four distance cells as the distance
join quotient developed by Alhevaz, Baghipur, Ganie and Shang.
[Distance join spectrum](https://doi.org/10.3390/sym12010169)
