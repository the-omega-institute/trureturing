---
bibkey: fucci2024poschlteller
authors: Guglielmo Fucci; Jonathan Stanfill
year: 2024
title: "The exotic structure of the spectral ζ-function for the Schrödinger operator with Pöschl–Teller potential"
doi: 10.1007/s00023-025-01587-7
url: https://arxiv.org/abs/2411.17860v1
claim: "Remark B.3 conjectures that all g_{m,j}(p/q,β) are nonzero for the considered coprime 0 < p < q and nondegenerate β; the coefficient g_{3,1}(2/3,π/4) vanishes."
strata_touched:
  - D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.1007/s00023-025-01587-7

Source: https://arxiv.org/abs/2411.17860v1

Appendix B, Remark B.3, printed page 31 (continuing on page 32), states:

> From calculations performed for particular choices of $p$, $q$, and $\beta$, we in fact conjecture that all of the $g_{m,j}(p/q,\beta)$ are nonzero for the choices of $p,\ q,$ and $\beta$ considered here.

The journal locator is Annales Henri Poincaré 27 (2026), 2073–2116.
The journal text retains Remark B.3.

## Coefficient definitions

Appendix B's general definitions determine the coefficients; the special
display of $\mathcal P_1$ is not used as a definition. The manuscript labels
used here are (B.17), $C_m$, $G_k$, $\mathcal P_k$, $\mathcal E_j$,
(B.24)–(B.26), and (B.39)–(B.45). The typeset arXiv PDF numbers the
final coefficient expansion (B.48).

The generalized Bernoulli convention is DLMF 24.16.1:

$$
\left(\frac{t}{e^t-1}\right)^a e^{xt}
=\sum_{n=0}^{\infty}B_n^{(a)}(x)\frac{t^n}{n!}.
$$

For real $a$, the power is the binomial series with descending Pochhammer
coefficients. Mathlib's `bernoulliPowerSeries` supplies $t/(e^t-1)$.
With $T$ representing the common logarithmic denominator factor,
$\mathcal E_0=1$ and $\mathcal E_j=E_jT/2$ for $j\ge1$.

$$
\begin{aligned}
C_m(y)&=\sum_{j=0}^{m-1}\binom{2m-1}{2j}
  \frac{2^{2m}y^{2j}}{m-j}B_{2(m-j)},\\
E_k(y)&=2(2y)^{2k-1}-\frac{(2y)^{2k}}{k}-C_k(y),\\
G_k(x,y)&=\binom{x-y}{k}B_k^{(x-y+1)}(x),\\
\mathcal P_0(y)&=1,\qquad
\mathcal P_k(y)=\sum_{j=0}^{k}4^{k-j}\mathcal E_j(y)G_{2(k-j)}(1-y,y)
\quad(k\ge1).
\end{aligned}
$$

The factor $\Omega_0$ is
$2^{2\nu-1}\Gamma(1+\nu)\cot(\beta)e^{i\pi\nu}/\Gamma(-\nu)$.
Writing $y_\pm=(1\pm\nu)/2$, (B.24)–(B.26) give
$\bar{\mathcal P}_k=\Omega_0\mathcal P_k(y_+)$ and
$\Omega_k=\bar{\mathcal P}_k-\sum_{l=0}^{k-1}\mathcal P_{k-l}(y_-)\Omega_l$.
The coefficient of $x^{m+p}$ in
$\log(1+\sum_{k\ge0}\Omega_k x^{p+kq})$ is $\mathcal S_m$;
the coefficient of $T^j$ in $\mathcal S_m$ is $g_{m,j}$.
The admissible indices satisfy $lp+kq=m$ with $l,k\in\mathbb N_0$,
and $k_m$ is the largest such $k$.

Printed page 31 states:

> The order of $\mathcal S_m(p/q,z)$ is, then, $k_m=\textrm{max}\{k_i\}$ with $i\in\mathbb N$, namely the largest value of $k_i$ amongst the vectors $(l_i,k_i)\in[m]_{p,q}$.

## Reflection cancellation and scope

The Lean module proves the counterexample
$(p,q,\beta,m,j)=(2,3,\pi/4,3,1)$ directly from these definitions.
At this order the formal logarithm contributes only $\Omega_1$.
Since $G_0=1$, the $T$-coefficient of $\mathcal P_1(y)$ is $E_1(y)/2$.
The identity $E_1(1-y)=E_1(y)$ cancels that coefficient at $y_+$ and $y_-$.
The compiled private calculation gives $g_{3,1}(2/3,\beta)=0$ for every
real $\beta$; the public result refutes the source's universal conjecture.

The family $g_{q,1}(p/q,\beta)=0$ for all coprime $0<p<q$ follows in
prose from $(n-1)p+kq=q$. For $p\ge2$ the only pair is $(n,k)=(1,1)$;
for $p=1$ the additional term $(q+1,0)$ is independent of $T$.
This all-parameter family is not a theorem in this Lean module.
For $p\ge2$, the prose calculation gives
$g_{q,0}=\Omega_0\nu(\nu^2-1)/3\ne0$ in the source's nondegenerate range.
Consequently the source's assumption that all these coefficients are
nonzero has no instance, and its $j=1$ branch-point contribution at
$m=q$ is absent. These analytic interpretations use the source's
expansion; spectral continuation is not formalized here.

## Computed evidence and remaining questions

The experiment entry
[`docs/reports/fucci-stanfill-2024-poschl-teller-coefficients/check.py`](https://github.com/the-omega-institute/trureturing-experiments/blob/0e97aabf0e76c8d278d29e9a3b66ff6a2207e66e/docs/reports/fucci-stanfill-2024-poschl-teller-coefficients/check.py)
has SHA-256 `50fcf972778131ed652e02d4b8998daea3dcb0f7e17a7042835b3ddded112909`.
The supplied reading is `python3 check.py`, exit 0, final line `ALL_OK`.
It checks every coprime $0<p<q\le8$, with symbolic $\Omega_0$ and
arbitrary higher coefficients. This is computed evidence, not a Lean
proof of the family.

It also checks the discrepancy in (B.21): the general definitions give
the $T$-coefficient $-(6y^2-6y+1)/3$, whereas the displayed expression
prints $-(6y^2-6y-1)/3$. Both are reflection symmetric, so either gives
the same cancellation. This discrepancy is a computed source correction.

Open: classify other vanishing $g_{m,j}$, especially top-order terms
arising from one reflection-symmetric product. Open: determine whether
restrictions such as $j\ge2$ or $m\notin q\mathbb N$ give a corrected
genericity hypothesis for Sections 3.1.1–3.1.2.
