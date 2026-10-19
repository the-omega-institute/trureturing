---
bibkey: janssen2025annealedpotts
authors: A. J. E. M. Janssen
year: 2025
title: "Analysis of quantities determining the critical inverse temperature in the annealed Potts model with Pareto vertex weights"
doi: null
url: https://arxiv.org/abs/2508.21409v3
claim: "With F0(t) = E[W/E[W] (e^{tW}-1)/(e^{tW}+q-1)] first positive and then negative in its second derivative, t_c is the unique positive zero of K(t) = E[ln((e^{tW}+q-1)/q)]/E[W] - ((q-1)/(2q)) t F0(t) - t/q; the paper suggests from limited numerics that 2 (mu_3/mu_4) ln(q-1) < t_c < 2 (mu_0/mu_1) ln(q-1) for q > 2 and general weight densities."
strata_touched:
  - D5/S3/StatisticalMechanics/AnnealedPottsMomentBoundRefutation
license: citation-only
triage: anchor
---

# Analysis of quantities determining the critical inverse temperature in the annealed Potts model with Pareto vertex weights

A. J. E. M. Janssen, arXiv:2508.21409v3 (math-ph), 2026-07-14; v1 2025-08-29. Quotations are from the v3 TeX source.

The order parameter and the standing assumption (Section 1):

> \caf_0(t)=\dE\,\Bigl[\frac{W}{\dE\,[W]}~\frac{e^{tW}-1}{e^{tW}+q-1}\Bigr]~,~~~~~~ t\geq0~.
> Assume that $\caf_0''(t)$ is first positive and then negative, so that $\caf_0(t)$ has a unique inflection point $t_{\ast}>0$

The criticality function (Section 1, Eq. (6)):

> \cak(t)=\frac{1}{\dE\,[W]}\,\dE\,\Bigl[{\rm ln}\Bigl(\frac{e^{tW}+q-1}{q}\Bigr)\Bigr] -\frac{q-1}{2q}\,t\,\caf_0(t)-\frac{t}{q}~,~~~~~~ t\geq0~,
> By \cite{ref1}, Theorem~1.14, $t_c$ is the unique $t>0$ such that $\cak(t)=0$

The proposed general bounds (Section 6):

> In fact, a limited numerical exploration with some other pdfs (like the exponential $\exp({-}w)\,\cax_{[0,\infty)}(w)$ and $\cax_{[0,1)}(w)$) shows that there may hold more generally
> 2\,\frac{\mu_3}{\mu_4}\,{\rm ln}(q-1)<t_c<2\,\frac{\mu_0}{\mu_1}\,{\rm ln}(q-1)~, ~~~~~~q>2~,

## Verified locator

- URL: https://arxiv.org/abs/2508.21409v3 (v3, 2026-07-14; v1, 2025-08-29; source `2026juliArxiv.tex`, md5 `ed38ab9de534739f661e30e0bcee3032`): Eq. (1) and the standing assumption (l. 35–38), Eq. (6) and the uniqueness of t_c (l. 55–58), the proposed general bounds (l. 480–487).
