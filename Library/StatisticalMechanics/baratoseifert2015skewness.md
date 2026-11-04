---
bibkey: baratoseifert2015skewness
authors: Andre C. Barato, Udo Seifert
year: 2015
title: "Skewness and Kurtosis in Statistical Kinetics"
doi: 10.1103/PhysRevLett.115.188103
url: https://arxiv.org/abs/1510.03279v1
claim: "For unicyclic enzymatic schemes with an irreversible product release, the randomness parameter, skewness and kurtosis of the cycle completion time are bounded above by 1, 2 and 9; for a four-state two-cycle scheme the paper finds numerically that a constraint S <= 2 keeps the randomness parameter at most 1, and leaves open whether this ordering holds for arbitrary networks that do not consist of a single cycle."
strata_touched:
  - D5/S3/StatisticalMechanics/WaitingTimeRandomnessSkewnessRefutation
license: citation-only
triage: anchor
---

# Barato–Seifert, skewness and kurtosis in statistical kinetics

## Verified locator

DOI: 10.1103/PhysRevLett.115.188103

Source: https://arxiv.org/abs/1510.03279v1

Phys. Rev. Lett. 115, 188103 (2015).

A. C. Barato and U. Seifert, arXiv:1510.03279v1 [cond-mat.stat-mech] (12 October 2015, the only version); Phys. Rev. Lett. 115, 188103 (2015). Quotations are from the v1 TeX source `skewkurtstatkinarxiv.tex`, with macros for $\mathcal R,\mathcal S,\mathcal K$ written out.

The cycle completion time and its moments (l. 132–153):

> The probability that a cycle is completed at time $t$ is denoted by $\psi(t)$. Its moment of order $n$ is defined as $t_n\equiv \int_0^\infty \psi(t)t^n$.

> $\mathcal R\equiv \sigma^2/t_1^2$, where $\sigma\equiv \sqrt{t_2-t_1^2}$. […] the skewness $\mathcal S\equiv (t_3-3t_1 \sigma^2 -t_1^3)/\sigma^3$, and the kurtosis $\mathcal K\equiv (t_4-4t_3t_1+6\sigma^2t_1^2+3t_1^4)/\sigma^4$.

A cycle is completed by the irreversible product-release transition (eq. `fullreaction`: "The last transition is taken to be irreversible").

The ordering and the open question (l. 341–358):

> The maxima of randomness parameter $\mathcal R$, skewness $\mathcal S$ and kurtosis $\mathcal K$ for a unicyclic network are $\mathcal R=1$, $\mathcal S=2$, and $\mathcal K=9$ […] This numerical investigation consists of, for example, maximizing the skewness with the constraint that $\mathcal R\le 1$, which leads to a skewness exceeding $2$. The opposite however is not possible, if the constraint $\mathcal S\le 2$ is satisfied, the randomness parameter never goes above $1$. […] It remains as an open question whether this property is true for arbitrary networks that do not consist of a single cycle.

## Encoding and boundary

A network is a finite rate matrix on `Fin m` with nonnegative off-diagonal rates and a marked product-release transition $p\to r$ with positive rate, from which $p$ is reachable from every state. The cycle completion time is the first time the marked transition fires after a release into $r$. Its moments are the first-passage moments $m_n$ with $m_0=1$ and $(-G)m_n=n\,m_{n-1}$, where $G$ is the generator with the marked transition sent to a cemetery; $t_n=m_n(r)$. This is the standard phase-type characterization of the moments of $\psi$, used in place of the source's generating-function route; $\mathcal R$ and $\mathcal S$ are the source's formulas in these moments.

The repository refutes the ordering for arbitrary networks with an eight-state network of two routes sharing the product edge (a fast route through one intermediate and a slow five-stage route), for which $\mathcal R=\frac{2257}{1089}>1$ while $0<\mathcal S<2$. The unicyclic bounds, the kurtosis part of the ordering and reversible perturbations are outside this conclusion.
