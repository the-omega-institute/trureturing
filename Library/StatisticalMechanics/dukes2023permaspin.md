---
bibkey: dukes2023permaspin
authors: Mark Dukes
year: 2023
title: "An Ising model having permutation spin motivated by a permutation complexity measure"
doi: 10.1016/j.physa.2023.129090
url: https://arxiv.org/abs/2211.08908v3
claim: "The paper introduces the permaspin model, an Ising-type model whose spins are permutations with an interaction energy given by a permutation statistic, solves the one-dimensional model without external field through the statistic's generating function, writes the partition function of the one-dimensional 3-permaspin model in an external field through a 6x6 symmetric transfer matrix whose eigenvalues are c(1-d)^2, c(1-d^2) and the three roots of an explicit cubic, observes numerically that the largest root of the cubic is the largest eigenvalue, and states the free energy conditionally on that observation."
strata_touched:
  - D5/S3/StatisticalMechanics/PermaspinTransferEigenvalueOrder
license: citation-only
triage: anchor
---

# Dukes, the permaspin model

M. Dukes, arXiv:2211.08908v3 [math.CO] (22 July 2023; v1 16 November 2022); Physica A 626 (2023) 129090. Quotations are from the v3 TeX source, with cross-references omitted.

The 1D 3-permaspin model in an external field (Section 4): $Z_n=e^{\beta(J+H)n}\operatorname{Tr}(A^n)$ for a real symmetric $6\times6$ matrix $A$ with entries $a^{\mathrm{stat}(\pi)+\mathrm{stat}(\sigma)}b^{\mathrm{stat}(\pi^{-1}\sigma)}$, $a=e^{H'/2}$, $b=e^{J'}$. With $c=a^4$ and $d=b^2$, its eigenvalues are $\lambda_4=c(1-d)^2$, $\lambda_5=c(1-d^2)$ and the three roots of

$t(\lambda)=\lambda^3-(cd^2+c^2+2cd+c+1)\lambda^2-c(cd^3+3c^2d+cd^2+c^2+cd+c+3d+1)(d-1)\lambda+(d^2+4d+1)c^3(d+1)(d-1)^3$.

The observation:

> Let $\lambda^{*}$ be the largest root of $t(\lambda)=0$. It remains to see which of the eigenvalues $\lambda^{*}$, $\lambda_4$, and $\lambda_5$ is largest. Numerical investigations indicate that $\lambda^{*}$ appears to be the largest and this is supported by the evidence presented by in Figures 1 and 2.

The following proposition gives the free energy under the hypothesis $\lambda^{*}=\max(\lambda^{*},\lambda_4,\lambda_5)$.

## Verified locator

Source: https://arxiv.org/abs/2211.08908v3
- DOI: https://doi.org/10.1016/j.physa.2023.129090 (Physica A 626 (2023) 129090; author, journal, volume and article number from Crossref).
- URL: https://arxiv.org/abs/2211.08908v3 (the e-print is a gzipped tar archive; member `permaspin.tex`, 822 lines, md5 `195dcf36a14b474bf17da29f39a275c5`):
  - the transfer matrix and its characteristic polynomial, l. 451–489;
  - the eigenvalues $\lambda_4$, $\lambda_5$, l. 490–503;
  - the cubic $t$, l. 504–509;
  - the observation, l. 510–513;
  - the conditional free-energy proposition, l. 515–532.
- The arXiv version dates are from the arXiv metadata.
