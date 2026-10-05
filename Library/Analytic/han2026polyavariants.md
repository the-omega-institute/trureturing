---
bibkey: han2026polyavariants
authors: Songlin Han
year: 2026
title: "On variants of Pólya's conjecture"
doi: null
url: https://arxiv.org/abs/2608.27130v1
claim: "Theorem 1.1 makes eventual nonnegativity of a specified Liouville Riesz sum sufficient for RH; the reverse asymptotic in Theorem 1.2 and Corollary 1.3 also assumes simple zeros and an absolute zero-sum condition."
strata_touched: []
license: citation-only
triage: anchor
---

# A one-sided Liouville sign criterion

The primary version is [arXiv:2608.27130v1](https://arxiv.org/abs/2608.27130v1),
submitted 27 August 2026, 17 pages. The inspected scope is the definitions,
Theorems 1.1–1.2, hypotheses H1–H3 and Corollary 1.3 on printed pages 3–4.
The complete contour argument and its zero-series estimates are not independently
certified here. The source is a preprint, not a Lean proof or an unconditional
RH resolution. No source text is vendored.

With the Liouville function $\lambda(n)=(-1)^{\Omega(n)}$, the paper fixes

$$
f(x)=-\sum_{n\le x}\frac{\lambda(n)\log n}{\sqrt n}\log\frac xn.
$$

Theorem 1.1 states

$$
\bigl[\exists x_0\ge2\ \forall x\ge x_0:\ f(x)\ge0\bigr]
\quad\Longrightarrow\quad\mathrm{RH}.
$$

The converse in Theorem 1.2 uses three premises: RH, simplicity of every
nontrivial zero, and

$$
\sum_{\gamma>0}
\frac{|\zeta(1+2i\gamma)|}
{\gamma^2|\zeta'(1/2+i\gamma)|}<\infty.
$$

Under those premises Corollary 1.3 gives
$f(x)\sim(\log x)^3/[12|\zeta(1/2)|]$ and eventual positivity. It is therefore
incorrect to quote the source as establishing this converse from RH alone.
The source's Dirichlet series is $\zeta(2s)/\zeta(s)$; its pole structure and
its specific logarithmic Riesz weight are part of the criterion.

For the actual FIB coefficient $e=\mu*\beta$, the already available
Dirichlet inverse $\gamma=\beta^{-1}$ recovers $\mu=\gamma*e$. The classical
square-indicator convolution $\lambda=\mu*\mathbf1_{\mathrm{square}}$
then identifies a possible common-source transport. Neither inverse
convolution nor Riesz weighting preserves pointwise signs automatically.
The formula $I_\psi(x)=\sum_m H_mJ_x(m)$ in FIB §397 does not identify
$I_\psi$ with this $f$, and positivity of a single $J_x(m)$ does not verify
Theorem 1.1's quantified condition. Any application must recover the
complete actual Liouville sum and prove its eventual sign.
