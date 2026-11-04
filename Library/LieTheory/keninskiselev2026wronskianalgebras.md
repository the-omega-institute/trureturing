---
bibkey: keninskiselev2026wronskianalgebras
authors: Markuss G. Ķēniņš; Arthemy V. Kiselev
year: 2026
title: "Explicit class of finite-dimensional polynomial algebras with Wronskians over R^d as N-ary Lie brackets: beyond sl(2)"
doi: null
url: https://arxiv.org/abs/2605.27305v2
claim: "The paper studies finite-dimensional polynomial N-ary SH-Lie algebras in d variables with the complete generalised Wronskian of order k as bracket, shows that with a monomial of degree k+1 on top of the polynomials of degree at most k the algebra is perfect only for d=1 or d=2, k=1, gives perfect examples with homogeneous polynomials for d=2,3 and k=1, and asks whether for every d>=2 and k>=1 some homogeneous polynomial of degree k+1 makes the algebra perfect."
strata_touched:
  - D5/S3/HomologicalAlgebra/WronskianPerfectLonelyAlgebra
license: citation-only
triage: anchor
---

# Explicit class of finite-dimensional polynomial algebras with Wronskians

M. G. Ķēniņš and A. V. Kiselev, arXiv:2605.27305v2 (10 July 2026; v1 26 May 2026). Quotations are from the v2 TeX source, with the macros `\Bbbk`, `\bx`, `\EuA`, `\Bone` and `\wedges` written as $\Bbbk$, $\boldsymbol x$, $\mathcal A$, $\mathbf 1$ and $\wedge\cdots\wedge$, and cross-references omitted.

Notation: $\Bbbk=\mathbb R$ or $\mathbb C$ is the base field; $\Bbbk_k[x^1,\dots,x^d]$ denotes the polynomials of degree at most $k$; for a multi-index $\vec r\in\mathbb N_{\ge0}^d$, $\partial^{|\vec r|}/\partial\boldsymbol x^{\vec r}=\partial^{r^1}_{x^1}\cdots\partial^{r^d}_{x^d}$.

The bracket:

> The $N$-linear (over $\Bbbk$) totally antisymmetric, $C^\infty(\mathbb R^d)$-valued differential operator $W_d^k=\mathbf 1\wedge\partial_{\boldsymbol x}\wedge\cdots\wedge\partial^k_{\boldsymbol x\dots\boldsymbol x}$ is the complete generalised Wronskian determinant of differential order $k$ over dimension $d$.

Here $N=\binom{d+k}{k}$, and the rows of the determinant are the operators $\partial^{|\vec r|}/\partial\boldsymbol x^{\vec r}$ with $|\vec r|\le k$, each once.

Perfectness:

> we say that the polynomial $N$-ary SH-Lie algebra $\mathcal A$ with the Wronskian $W_{d\geqslant 1}^{k\geqslant 1}$ as the bracket is perfect if the bracket spans the whole algebra: $\operatorname{Span}_\Bbbk W_d^k(\mathcal A,\dots,\mathcal A)=\mathcal A$.

Examples: $\langle1,x,y,xy\rangle$ for $d=2$, $k=1$, and $\langle1,x,y,z,xy+yz+zx\rangle$ for $d=3$, $k=1$, are perfect; with a monomial of degree $k+1$ on top of $\Bbbk_k[\boldsymbol x]$ the algebra is perfect only for $d=1$ or for $d=2$, $k=1$.

The open problem:

> Let the base dimension $d\geqslant 2$ and differential order $k\geqslant 1$ be arbitrary. Put the complete generalised Wronskian $W_d^k$ as the $N$-ary bracket, $N={d+k\choose d}$, on the $N$-ary SH-Lie polynomial algebra $\Bbbk[x^1,\dots,x^d]$. Does there exist an homogeneous polynomial $p(\boldsymbol x)\in\Bbbk[\boldsymbol x]$ of degree $k+1$ such that the $N$-ary SH-Lie polynomial subalgebra $\mathcal A=\Bbbk_k[\boldsymbol x]\oplus\langle p(\boldsymbol x)\rangle$ is perfect w.r.t the Wronskian, i.e. $\operatorname{Span}_\Bbbk W_d^k(\mathcal A,\dots,\mathcal A)=\mathcal A$?

## Verified locator

Source: https://arxiv.org/abs/2605.27305v2
- URL: https://arxiv.org/abs/2605.27305v2 (the e-print is a tar archive; member `FinDim220526v2.tex`, 2221 lines, md5 `777135f176c9db701f21e5554216fb33`):
  - perfectness, Definition `def:perfect-lie-algebra`, l. 517–521;
  - notation, l. 538–542 and Notation `not:multi-index`, l. 613–623;
  - the Wronskian, Definition `def:wronskian`, l. 625–627;
  - the example for $d=2$, Example `ex:dimension-two-closed-old`, l. 467–478;
  - monomial imperfection, Proposition `prop:imperfection`, l. 1198;
  - the example for $d=3$, Example `ex:perfection`, l. 1247–1255;
  - the open problem, Open problem `open:perfect-algebras`, l. 1258–1260.
- The author list and dates are from the TeX `\author` fields and the arXiv metadata; Crossref lists no journal version.
