---
bibkey: bohac2025biasclassqram
authors: Leonardo Bohac
year: 2025
title: "Bias-Class Discrimination of Universal QRAM Boolean Memories"
doi: 10.48550/arXiv.2512.17503
url: "https://arxiv.org/abs/2512.17503v1"
claim: "The paper derives the single-query ensemble state and the single-copy Helstrom test for exact-weight bias classes of Boolean memories queried through a universal QRAM, gives a separable multi-query strategy based on the count of plus outcomes, and leaves open whether that count statistic is sufficient for optimal discrimination."
strata_touched:
  - D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency
license: citation-only
triage: anchor
---

# Bohac, Bias-Class Discrimination of Universal QRAM Boolean Memories

L. Bohac, arXiv:2512.17503v1 (2025). Quotations are from the v1 TeX source.

A Boolean memory $f:[N]\to\{0,1\}$ with $N=2^n$ is drawn once under a hypothesis and kept fixed; each query returns the address state $|\psi_f\rangle=N^{-1/2}\sum_x(-1)^{f(x)}|x\rangle$. For the exact-weight class $\mathcal F(m)$ with the uniform prior, $t$ queries give the induced state

$$\rho_p^{(t)}=\mathbb E_{f\sim\mathcal F(m)}\big[(|\psi_f\rangle\langle\psi_f|)^{\otimes t}\big],$$

which need not factor as $\rho_p^{\otimes t}$. The separable strategy of Theorem 5.1 measures $\{|+\rangle\langle+|,\Pi_\perp\}$ on each register and tests on the number $k$ of "$+$" outcomes, with $k\sim\mathrm{Binomial}(t,\mu^2)$ and $\mu=1-2m/N$. Remark 5.3 states:

> An interesting open problem is to characterize the optimal error exponent for distinguishing these *exchangeable* but potentially correlated mixtures, and to determine whether the "$|+\rangle$-count" statistic is sufficient for optimal discrimination in the exact-weight prior model.

## Verified locator

Source: https://arxiv.org/abs/2512.17503v1
- DOI: https://doi.org/10.48550/arXiv.2512.17503 (the arXiv-issued DataCite DOI; title, author and year from DataCite; the abstract page lists v1 only).
- URL: https://arxiv.org/abs/2512.17503v1. The e-print member `bias_class_discrimination.tex` has 570 lines and md5 `40312fa46860afbd9a187fe64b700f86`. Locations:
  - the persistent-memory model, l. 95 and 255–256; the address state, l. 169–174;
  - exact-weight classes (Definition, $m\in\{0,\dots,N\}$), l. 244–250;
  - the $t$-copy induced state, l. 397–402;
  - Theorem 5.1 (the count strategy), l. 404–418;
  - Remark 5.3 (the open questions), l. 454–457.
