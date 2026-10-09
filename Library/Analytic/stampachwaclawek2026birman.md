---
bibkey: stampachwaclawek2026birman
authors: František Štampach; Jakub Waclawek
year: 2026
title: "Optimal discrete p-Hardy–Rellich–Birman inequalities"
doi: null
url: https://arxiv.org/abs/2605.25238v1
claim: "Conjecture 5.6(iii) asserts a convergent expansion in negative powers of n with entirely non-negative coefficients for the alternative Birman weight at every positive order and p > 1."
strata_touched: []
license: citation-only
triage: anchor
---

## Verified locator

DOI: null

Source: https://arxiv.org/abs/2605.25238v1

Section 2, equations (2.2) and (2.3), pp. 3–4, define the difference
operators, nonlinear discrete p-Laplacian and signed-power convention.
Equation (2.15) and Remark 2.12, p. 8, specify the normalized convergent
series and explain the proposed improvement by truncation. Equations
(2.16) and (2.17), p. 9, define the alternative parameter sequence and
its weight. Section 5, Conjecture 5.6, p. 28, states the three conjectural
properties of that alternative weight.

Crossref's bibliographic query for the exact title and both authors returns
no matching work DOI. The arXiv version is the source locator.

# The alternative discrete Birman weight

Conjecture 5.6 starts with:

> Let $\ell\in\mathbb N$ and $p>1$, and let $\tilde{\rho}^{(\ell,p)}$ be defined by (2.17) and (2.16).

Part (iii), p. 28, states verbatim:

> For all $n\geq\ell$, the terms $\tilde{\rho}_{n}^{(\ell,p)}$ admit a power series expansion in negative powers of $n$ with entirely non-negative coefficients; cf. (2.15).

The real sequence used here is literally (2.16):

$$
\tilde{\mathfrak g}_n^{(\ell,p)}=n^{1-1/p}\prod_{j=1}^{\ell-1}(n-j)
\quad(n\in\mathbb N_0),\qquad
\tilde{\mathfrak g}_n^{(\ell,p)}=0\quad(n<0).
$$

Equation (2.2) defines $(\nabla u)_n=u_n-u_{n-1}$ and
$(\mathrm{div}\,u)_n=u_{n+1}-u_n$. Equation (2.3) defines
$-\Delta_p^{(\ell)}u=(-1)^\ell\mathrm{div}^{\ell}(\nabla^{\ell}u)^{\langle p-1\rangle}$,
where $\nu^{\langle a\rangle}=\nu|\nu|^{a-1}$ and
$0^{\langle a\rangle}=0$. Equation (2.17) divides this expression for
$u=\tilde{\mathfrak g}$ by $(\tilde{\mathfrak g}_n)^{p-1}$.

In the convergent (2.15) normalization, let
$c_0=(1/q)_\ell^p$ and $c_k=c_0A_k$ for $k\geq1$.
Since $p>1$ and $\ell\geq1$, $c_0>0$. Non-negative normalized
coefficients therefore imply the weaker assertion encoded by `claim`:
there is one non-negative coefficient sequence giving
$n^{\ell p}\tilde\rho_n$ for every $n\geq\ell$.

At $\ell=2$ and $p=11/10$, rational enclosures at $n=100,200,400$
force the secant slopes at $x=1/n$ to decrease. Non-negative
power-series coefficients force those slopes to increase, so the
alternative weight has no such expansion. This refutes only part (iii).

Remark 2.12 concerns the source's original weight $\rho$, whereas
Conjecture 5.6 concerns $\tilde\rho$. The positivity results for
$\ell=1$ and $p=2$ remain applicable; the failure for the alternative
weight does not refute the original-weight conjecture in Remark 2.12.

Citation only; no source PDF or TeX is redistributed.
