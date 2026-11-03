---
bibkey: maweigert2025logfunctions
authors: Rourou Ma; Julian Weigert
year: 2025
title: "Complete monotonicity of log-functions"
doi: 10.1007/s13324-025-01136-9
url: https://arxiv.org/abs/2505.04225v2
claim: "The paper studies the functions p(log x_1, ..., log x_s)/(x_1 ... x_s) with p a polynomial of total degree at most n, shows that their completely monotone members form a semialgebraic cone, proves that in one variable and degree two the regions cut out by the sign conditions on single derivatives form a descending chain, and conjectures that for every degree these regions form a descending chain converging to the completely monotone cone."
strata_touched:
  - D5/S3/Analytic/LogFunctionMonotoneChain
license: citation-only
triage: anchor
---

# Complete monotonicity of log-functions

R. Ma and J. Weigert, arXiv:2505.04225v2; Analysis and Mathematical Physics 15(6) (2025), 141. Quotations are from the v2 TeX source, with the macros `\RR`, `\NN`, `\F`, `\CM` and `\dd` written out and `\emph` dropped.

Complete monotonicity:

> Consider an infinitely differentiable function $f:\mathbb R_{>0}^s\to \mathbb R$. The function $f$ is said to be completely monotone (on the positive orthant) if $\forall\alpha\in \mathbb N_0^s:\forall x\in \mathbb R_{>0}^s: \prod_{i=1}^s\left(\frac{-\partial }{\partial x_i}\right)^{\alpha_i}f(x_1,\ldots,x_s) \geq 0$

The function class:

> $\mathcal{F}_{s,n}:=\left\{f\in \mathcal{C}^\infty(\mathbb R_{>0}^s,\mathbb R) \middle| \exists p\in \mathbb R[{\bf y}]_n: \forall x \in \mathbb R_{>0}^s: f(x)=\frac{p(\log(x_1),\ldots, \log(x_s))}{x_1\cdots x_s}\right\}$

Here $\mathbb R[{\bf y}]_n$ is the space of real polynomials in $s$ variables of total degree at most $n$, and $\mathrm{CM}_{s,n}:=\mathrm{CM}_s\cap\mathcal F_{s,n}$.

The conjecture (Conjecture `conj:shrinking`):

> For any $n\in \mathbb N$ the semialgebraic sets $D_k=\left\{f\in \mathcal{F}_{1,n}\middle|\forall x\in \mathbb R:\left(\frac{-\mathrm d}{\mathrm dx}\right)^kf(x)\geq 0\right\}$ form a descending chain under inclusion, i.e. $D_k\supseteq D_{k+1}$, which converges to the region $\mathrm{CM}_{1,n}=\bigcap_{k=1}^\infty D_k$.

The members of $\mathcal F_{1,n}$ are functions on $\mathbb R_{>0}$, and the example preceding the conjecture states the sign conditions for $x\in\mathbb R_{>0}$.

## Verified locator

Source: https://arxiv.org/abs/2505.04225v2
- URL: https://arxiv.org/abs/2505.04225v2 (the e-print is a tar archive):
  - member `Intro.tex` (75 lines, md5 `273a80101f0cc7861d6932d5cf5568c8`): complete monotonicity, l. 1–4; the class $\mathcal F_{s,n}$, l. 19–23; $\mathrm{CM}_{s,n}$, l. 33;
  - member `infiniteOrderDeriv.tex` (159 lines, md5 `dee5d979f738ec3f47c4320538a59922`): the example with the sign conditions on $\mathbb R_{>0}$, l. 148–152; the conjecture, l. 154–159.
- DOI: 10.1007/s13324-025-01136-9 (https://doi.org/10.1007/s13324-025-01136-9; Crossref lists Analysis and Mathematical Physics, volume 15, issue 6, article 141, published 6 November 2025).
