---
bibkey: wormald2026tournaments
authors: N. C. Wormald
year: 2026
title: Tournaments with many Hamilton cycles
doi: null
url: https://arxiv.org/abs/2610.16245
claim: 'Conjecture 6: For every regular tournament T* on at least three vertices, H is nonzero and d/H is the square of a rational.'
strata_touched:
  - D5/S3/Combinatorics/WormaldTournamentHessian/Result
license: citation-only
triage: anchor
---

# Tournaments with many Hamilton cycles

## Verified locator

https://arxiv.org/abs/2610.16245

Author manuscript: https://users.monash.edu.au/~nwormald/papers/hamtourn.pdf

The source quotations below are supplied excerpts from section 1. Printed page
numbers and the complete manuscript have not been independently checked here.

## Source statements

§1, Conjecture 6:

> Conjecture 6. For every regular tournament $T^*$ on at least three vertices,
> ${\cal H}\neq 0$ and $d/{\cal H}$ is the square of a rational.

§1, equation (1.2) and its defining paragraph:

> Define $B$ to be the matrix whose $(i,j)$ entry $B_{ij}$ is $-y_j$ if $A_{ij}=1$ and 0 otherwise, except for diagonal entries $B_{ii}=1-\frac12 y_i$. That is, $B=I_d-(\frac12 I_d+A)D_y$ where $D_y=\operatorname{diag}(y_1,\ldots,y_d)$. Let $K=K(\mathbf y)=\det B$. Set $z=2/d$ and $\mathbf z=(z,z,\ldots,z)$.

§1, defining paragraphs immediately preceding Theorem 4:

> Writing $K_j$ for the partial derivative of $K$ with respect to $y_j$, it will be shown that $K_d(\mathbf z)\neq0$ and $K(\mathbf z)=0$, so (e.g. by observing that $K$ is linear in $y_d$) one may solve $K(\mathbf y)=0$ in the neighbourhood of $\mathbf z$ and obtain $y_d=h(y_1,\ldots,y_{d-1})$ for an analytic function $h$.
>
> Define a function $\tilde f$ in the neighbourhood of $(0,0,\ldots,0)$ (the $(d-1)$-dimensional vector) by $\tilde f(\theta_1,\ldots,\theta_{d-1})=\log h(ze^{i\theta_1},\ldots,ze^{i\theta_{d-1}})$.
>
> Let ${\cal H}$ denote the determinant of the Hessian (matrix of second order partials) of $\tilde f$ at $\theta_j=0$ for $j=1,\ldots,d-1$.

The supplied excerpt also states:

> it is unexplained why $d/{\cal H}$ turns out to be a perfect square in all
> the examples computed

> Presumably there is a more direct way to calculate this.

## Scope

The formal objects use zero-based vertex labels, retain the final vertex as the
implicit coordinate, and use the principal complex logarithm near the positive
real point $z$. The Hessian uses derivatives over the real angular domain.
The source uses an analytic local solution. The formal encoding asks only for
complex $C^2$ regularity at the base point, the local equation germ and its base
value; these suffice for the two derivatives. The formal claim includes existence
of such a solution and the same conclusion for every such local solution. A determinant identity alone is
not an identification with this analytic Hessian.
