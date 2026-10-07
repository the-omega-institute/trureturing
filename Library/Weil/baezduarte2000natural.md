---
bibkey: baezduarte2000natural
authors: Luis Báez-Duarte
year: 2000
title: Arithmetical Aspects of Beurling's Real Variable Reformulation of the Riemann Hypothesis
doi: null
url: https://arxiv.org/abs/math/0011254v1
claim: "Proposition 4.4 excludes full-sequence L2 convergence of the unbalanced natural Möbius prefixes on the half-line. It does not exclude every subsequence or freely chosen coefficients in the Nyman–Beurling criterion."
strata_touched: []
license: citation-only
triage: anchor
---

# The natural-prefix obstruction and its exact scope

The pinned source is [arXiv:math/0011254v1](https://arxiv.org/abs/math/0011254v1),
submitted 2000-11-29. The [21-page PDF](https://arxiv.org/pdf/math/0011254v1)
has SHA256 `951ecc56eaae5b80eb8128ab4f98b5184d06ed97da608a130d65940daea8e94c`.
The inspected [author TeX](https://arxiv.org/src/math/0011254v1)
has SHA256 `32453b451c900c7c557fc7da5eb8b93987d9d2addca4d31d293b9f844e84801d`.
The selected definitions, Proposition 4.4 and its proof, and the subsequent
scope distinctions were read. This is source reuse, not a new proof or a
Lean verification of the paper.

## Space, coefficients and cutoff

Section 1 works in $L^p((0,\infty),dx)$, defines
$\chi=\mathbf1_{(0,1]}$, and uses the fractional part $\rho(t)=t-\lfloor t\rfloor$.
Its dilation is $K_af(x)=f(ax)$. Equations (1.4) and (1.18) define
$g(n)=\sum_{k\le n}\mu(k)/k$ and the unbalanced natural prefix

$$
S_n(x)=\sum_{k=1}^n\mu(k)\rho\!\left(\frac1{kx}\right).
$$

Thus the approximation residual has sign $\chi+S_n$; it is not
$\chi-S_n$. The coefficient cutoff passes through all positive integers
$n$, and the half-line norm retains the region $x>1$.

Proposition 4.4, PDF p. 17, states that if $\zeta$ has a zero of real
part $1/p$, then $S_n$ and the associated balanced sequence $V_n$ do
not converge in $L^p$. In particular they do not converge in $L^2$.
This last conclusion uses the known existence of zeros on the critical
line, not RH. Its proof retains the tail $x>1/m$; equation (4.10)
under the assumed convergence yields

$$
\|\chi+S_m\|_p^p\ge
\frac{m^{p-1}}{p-1}|g(m)|^p.
$$

The paper combines that implication with the non-little-oh statement
(4.9). Proposition 4.5, PDF p. 18, also gives (4.11)–(4.12), including
$\|\chi+S_n\|_2\ge\sqrt n\,|g(n)|$. These are quoted source results;
no lower-bound scan is required to reuse them.

## What this obstruction does not say

Remarks 4.6 and the paragraph following Proposition 4.5 explicitly
discuss selected zero-crossing subsequences as unresolved possibilities
in this source. Full-sequence nonconvergence does not by itself exclude
all subsequences. A Fibonacci cutoff schedule would need a separate
argument; it cannot be rejected just by changing the index name in
Proposition 4.4.

Proposition 4.6, PDF p. 18, treats the distinct natural sequences $B_n$
and $F_n$. Proposition 4.7, PDF p. 19, treats fixed-coefficient series
in the balanced family $\mathcal C^{nat}$ on the unit interval. Neither
is silently substituted for Proposition 4.4 on the half-line.

The closure criterion permits coefficients depending on the cutoff.
Its natural-dilation form is already sourced in the
[2002 criterion note](baezduarte2002nyman.md). The proof in that source
uses damped coefficients and an order of limits; its Introduction also
discusses the logarithmically mollified Selberg approximation. Those
are different approximation problems from the unweighted $S_n$.
Pointwise or unit-interval $L^1$ convergence of natural prefixes supplies
neither half-line $L^2$ convergence nor an unconditional mollifier estimate.

## Interface with actual FIB coefficients

[FIB §391](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
uses the actual coefficients $e=\mu*\beta$ of §§384–386. The target
transported with those coefficients is $\Phi_\beta=\sum_d\beta_dK_d\chi$,
not the unchanged $\chi$. The prefix identity retains every $d>n$
target term. The dominant-head estimate already in §384 and the existing
Dirichlet-inverse budget supply an absolutely summable inverse.

That section's additional interface is a paper application of standard
dilation, convolution and convergence facts, not a new Nyman–Beurling
theorem or a claim of priority. The literature obstruction is used
directly. It does not settle actual FIB critical growth, a signed Robin
remainder or RH.
