---
bibkey: lahirichatterjeemaiti2007hypergeometric
authors: S. N. Lahiri, A. Chatterjee and T. Maiti
year: 2007
title: Normal approximation to the hypergeometric distribution in nonstandard cases and a sub-Gaussian Berry–Esseen theorem
doi: 10.1016/j.jspi.2007.03.033
url: https://arxiv.org/abs/math/0602276v1
claim: "The preprint's Theorem 2.2 bounds the hypergeometric distribution-function approximation error by order inverse standard deviation; Theorem 2.3 and Corollary 2.4 give nonuniform and sub-Gaussian tail bounds under their stated scale condition."
strata_touched: []
license: citation-only
triage: anchor
---

# Balanced hypergeometric maximum atoms and tail scales

## Verified locator

DOI: <https://doi.org/10.1016/j.jspi.2007.03.033> resolves with HTTP 200
to Elsevier's article identifier `S0378375807001188`. Crossref identifies
the authors, this title and *Journal of Statistical Planning and
Inference* 137(11), 3570–3590.
The accessible [arXiv version](https://arxiv.org/abs/math/0602276v1)
has the title *A Sub-Gaussian Berry-Esseen Theorem For the Hypergeometric
Distribution*. Its PDF archive stamp is 13 February 2006; its internal
title-page date is 13 August 2018. The 21-page PDF's parameter
definitions and Theorems 2.1–2.3 and Corollary 2.4 on PDF pp. 3–6
were inspected. The theorem numbering below refers to this preprint,
not an unchecked pagination of the publisher's full text.

## Classical approximation and the atom consequence

For a hypergeometric count with population $N$, marked population $R$,
sample size $U$, put $p=R/N$, $f=U/N$ and
$\sigma^2=Np(1-p)f(1-f)$. The exact variance is
$N\sigma^2/(N-1)$, so $\sigma$ is not literally the exact standard
deviation. Theorem 2.1 characterizes normal convergence by
$\sigma^2\to\infty$; Theorem 2.2 supplies the uniform order
$\Delta\le C/\sigma$ for the normal distribution-function error.

Comparing consecutive distribution-function values yields

$$
\mathbb P(T=t)
\le\Phi\!\left(\frac{t-Up}{\sigma}\right)
-\Phi\!\left(\frac{t-1-Up}{\sigma}\right)+2\Delta
\le\frac{1/\sqrt{2\pi}+2C}{\sigma}.
$$

For fixed $0<\rho\le1/2$ and both $p,f\in[\rho,1-\rho]$,
$\sigma\ge\rho(1-\rho)\sqrt N$. Thus the classical theorem
supplies the balanced order $\sup_t\mathbb P(T=t)\le C_\rho/\sqrt N$;
bounded small populations can be included by enlarging the constant.
This is a consequence of the published approximation mechanism,
not a new maximum-atom principle. No numerical optimal $C_\rho$ is asserted.

## Tails and native conditioning

Theorem 2.3 and Corollary 2.4 require $\delta\sigma>1$, with
$\delta$ specified by equation (2.12), and retain factors depending
on $p\wedge(1-p)$ in their sub-Gaussian bounds. The balanced regime
makes these factors uniform. The bounds are not uniform near
degenerate margins without retaining those conditions.

The [parity application](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
uses the exact conditional rectangle kernel and a weaker Chebyshev
tail. Establishing that kernel from the actual histories, preserving
the minimal conditioning, and controlling the shared moving posterior
denominator remain separate model-specific obligations. The
maximum-atom theorem supplies neither those relations nor the
modulo-one calibration bound.
