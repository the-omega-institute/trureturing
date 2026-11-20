---
bibkey: odorney2026pade
authors: Evan M. O'Dorney
year: 2026
title: "Two-point Padé approximation and patterns in continued fractions for (F_{n+1}/F_n)^k"
doi: 10.48550/arXiv.2611.01029
url: https://arxiv.org/pdf/2611.01029v1#page=16
claim: "Conjecture 4.7 asserts that the determinant in Exercise 4.6, equation (4.2), can vanish for nonzero integers a, b with positive discriminant only at k=4, i=3, a^2=b."
strata_touched:
  - D5/S1/Depth/ContinuedFractions/ODorneyPadeJunctionRefutation
license: citation-only
triage: anchor
---

# O'Dorney's Padé junction determinant

## Verified locator

DOI: 10.48550/arXiv.2611.01029

URL: https://arxiv.org/pdf/2611.01029v1#page=16

Section 4.2, p. 16, contains Exercise 4.6, equation (4.2), and Conjecture 4.7.
The SHA-256 of the v1 PDF is
`2d5c69837f39f5cab35d284f96e463a3f30eb06b12c2bbeb4fbb80b4c221170d`.
Exercise 4.1 appears on p. 15.

## Statement and counterexample

Conjecture 4.7, p. 16, reads

> The only solution to $\Upsilon_{k,i}(\alpha)=0$ with $a$, $b$ nonzero integers and
> $D=a^2+4b>0$ occurs at $k=4$, $i=3$, $a^2=b$, corresponding to the unique
> invisible junction in $a^4(F_{n+1}/F_n)^4$.

For $1\le i<k$, equation (4.2) gives the $(k-i)$-square determinant with
entry $\beta_{i+c-r}$ in zero-based row $r$ and column $c$. Exercise 4.6
defines $\beta_j$ as the coefficient of $X^{2i-j}$ in
$h(X)^{i-1}(X-\alpha)^2$, where $h(X)=X^2-aX-b$ and
$\alpha=(a+\sqrt D)/2$. Indices outside the coefficient range give zero.
The formal claim uses natural numbers for $k,i$ since $1\le i<k$ forces both
indices to be positive.

At $a=b=3$, $k=5$, and $i=4$, the determinant is the coefficient of $X^4$ in
$(X^2-3X-3)^3(X-\alpha)^2$. This coefficient is
$-54-54\alpha+18\alpha^2=18(\alpha^2-3\alpha-3)=0$ at the specified root.
The tuple also has $a>0$, $4^2<D=21<5^2$, and $b\mid a^2$ as in Exercise 4.1.
The determinant calculation leaves the existence of a patch-junction
decomposition for this tuple, the subdomain $b=\pm1$, and the separate
$\Delta$ determinant in Conjecture 4.5 open here.
