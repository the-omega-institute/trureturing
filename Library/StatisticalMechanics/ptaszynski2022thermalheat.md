---
bibkey: ptaszynski2022thermalheat
authors: Krzysztof Ptaszyński
year: 2022
title: "Bounds on skewness and kurtosis of steady state currents"
doi: 10.48550/arXiv.2204.08421
url: https://arxiv.org/abs/2204.08421v4
claim: "Equation (19) conjectures nonnegative heat-current kurtosis in classical Markovian systems driven only by temperature differences; equations (63)–(70) specify the thermal generator and cumulants."
strata_touched:
  - D5/S3/StatisticalMechanics/PtaszynskiThermalHeatKurtosisRefutation
license: citation-only
triage: anchor
---

# Thermal Markov heat-current kurtosis

## Verified locator

DOI: 10.48550/arXiv.2204.08421

Source: https://arxiv.org/abs/2204.08421v4

The journal version is Physical Review E 106, 024119 (2022), DOI 10.1103/PhysRevE.106.024119. The arXiv v4 text, Section III A, item 3, page 3, Eq. (19), states:

> In classical Markovian systems driven only by temperature differences kurtosis of the heat current is always nonnegative

The displayed inequality is $\mathcal K^h\ge0$. Equations (4) and (10), page 2, define $\mathcal K=\langle\!\langle j^4\rangle\!\rangle/\langle\!\langle j^2\rangle\!\rangle$ and $\langle\!\langle j^n\rangle\!\rangle=\left[\partial^n\chi(\lambda)/\partial\lambda^n\right]_{\lambda=0}$. These are scaled current cumulants.

Section III D, page 6, equations (63)–(70), gives the bath-resolved generator, local detailed balance, heat tilt and characteristic equation. The sentence following Eq. (64) is:

> where $k_{ij}$ is the transition rate from the state $j$ to $i$.

With directed rates $q_\alpha(i,j)=k_{ji}^\alpha$, the matrix entry in row $i$, column $j$ uses $q_\alpha(j,i)$, and the escape diagonal sums rates leaving the column state. Detailed balance reads $q_\alpha(i,j)/q_\alpha(j,i)=\exp(\beta_\alpha(E_i-E_j))$ on present edges. Absent edges have absent reverse edges. The counted-bath off-diagonal contribution is multiplied by $\exp(-\lambda(E_i-E_j))$ and the escape diagonal is unchanged.

Section III D, page 6, states:

> The cumulant generating function χʰ(𝝀) is then equal to the dominant eigenvalue of Wʰ(𝝀) [63]; however, its analytic calculation is usually not possible for N > 4.

The finite real-root formulation used in the accompanying module asks for a branch vanishing at zero, four times continuously differentiable there, and maximal among real characteristic roots at every real counting field. The refutation uses only the characteristic equation and the first two branch conditions. It does not separately prove existence of this branch or its identification with the physical scaled cumulant generating function.
