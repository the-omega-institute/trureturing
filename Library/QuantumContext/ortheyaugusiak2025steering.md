---
bibkey: ortheyaugusiak2025steering
authors: Alexandre C. Orthey; Remigiusz Augusiak
year: 2025
title: "Certifying classes of d-outcome measurements with quantum steering"
doi: 10.1088/1367-2630/adda73
url: https://arxiv.org/abs/2410.20477v2
claim: "The paper constructs steering inequalities that self-test classes of d-outcome measurements built from Heisenberg-Weyl operators with admissible phases, proves the self-testing statement, and for the robustness analysis with d > 3 assumes Conjecture 1: the transformed operators satisfy B̃_k^(n) = B̃_k^n for every prime d and every n in {1, …, d-1}, noted as true for d = 3."
strata_touched:
  - D5/S3/Quantum/Measurements/SteeringPowerPreservationRefutation
license: citation-only
triage: anchor
---

# Certifying classes of d-outcome measurements with quantum steering

A. C. Orthey Jr and R. Augusiak, arXiv:2410.20477v2 [quant-ph]; New J. Phys. 27 (2025). Quotations are from the v2 TeX source.

The reference measurements and their phases:

> where $\{\phi_{j,y}\}_{j=0}^{d-1}$ is a set of any real numbers satisfying $\sum_{j=0}^{d-1}\phi_{j,y}=0$ and $\oplus$ stands for addition modulo $d$.

The coefficients:

> $\gamma_{yk}^{(n)}\coloneqq \frac{1}{d}\omega^{kn(n-1)/2}\sum_{l=0}^{d-1}e^{-\bbm{i}\sum_{m=1}^{n}\phi_{l\oplus m,y}}\omega^{knl}$

The admissibility condition:

> $\sum_{k=0}^{d-1}\left(\gamma_{y'k}^{(n)}\right)^*\gamma_{yk}^{(n)} =\delta_{yy'},\qquad\forall y,y'.$

The substitution rule:

> $\left(XZ^k\right)^n\longrightarrow \widetilde{B}_k^{(n)}\coloneqq\sum_{y=0}^{d-1}\gamma_{yk}^{(n)}B_{n|y}$, where $B_y=\{B_{n|y}\}$, for $y=0,\ldots,d-1$ and $n=1,\ldots,d-1$, represent the $d$-outcome arbitrary measurements performed by Bob

Projective measurements:

> (i) Bob's measurements are projective, that is, all operators $B_{n|y}$ are unitary such that $B_{n|y}^d = \I$,

The robustness setting and Conjecture 1 (Appendix "Robust self-testing"):

> For simplicity, we will assume that the state is pure and the measurements performed by Bob are projective.

> To prove the robustness of our self-testing statement for the qutrit case, we will make use of the fact that $\widetilde{B}_k^{(n)}=\widetilde{B}_k^n, \quad \forall n\in\{1,2\}\quad\text{and}\quad d=3$, which is true from the fact that $\widetilde{B}_k^{(2)}=\left(\widetilde{B}_k^{(1)}\right)^\dagger$ and $\left(\widetilde{B}_k^{(2)} \right)^3=\I$. We can conjecture that the above relation is also valid for any prime $d>3$:

> **Conjecture 1.** For any prime $d$, we have that $\widetilde{B}_k^{(n)}=\widetilde{B}_k^n$, for every $n\in\{1,\ldots,d-1\}$. Note that this statement is true for $d=3$.

## Verified locator

Source: https://arxiv.org/abs/2410.20477v2
- URL: https://arxiv.org/abs/2410.20477v2 (source `main2.tex`, md5 `b3c5b40a34f721352981dcf58659087e`):
  - the phases, l. 190–194;
  - the coefficients, l. 204–206;
  - the admissibility condition, l. 234–236;
  - the substitution rule, l. 246–249;
  - projective measurements, l. 355;
  - the robustness setting, l. 1263;
  - Conjecture 1 and its context, l. 1265–1273.
- DOI: 10.1088/1367-2630/adda73 (https://doi.org/10.1088/1367-2630/adda73; Crossref lists New Journal of Physics, volume 27, issued 29 May 2025; arXiv lists v1 of 27 October 2024 and v2 of 18 May 2026).
