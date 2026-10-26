---
bibkey: vesperinibelhadjaissafranzosi2023entanglement
authors: Arthur Vesperini; Ghofrane Bel-Hadj-Aissa; Roberto Franzosi
year: 2023
title: "Entanglement and Quantum Correlation Measures from a Minimum Distance Principle"
doi: 10.1038/s41598-023-29438-7
url: https://arxiv.org/abs/2205.07143v2
claim: "The paper defines a quantum correlation distance (QCD) and, by minimizing it over decompositions of a mixed state and local rotations of each component, an entanglement distance (ED); it reports numerical evidence that on Bell-diagonal states the ED equals twice the squared concurrence."
strata_touched:
  - D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation
license: citation-only
triage: anchor
---

# Entanglement and Quantum Correlation Measures from a Minimum Distance Principle

A. Vesperini, G. Bel-Hadj-Aissa and R. Franzosi, arXiv:2205.07143v2 (2022-10-09); published as "Entanglement and quantum correlation measures for quantum multipartite mixed states", Sci. Rep. 13, 2852 (2023). Quotations are from the v2 TeX source.

The site QCD:

> we obtain the closed-form expression for the QCD of $\rho$, $C(\rho) =\sum^{M-1}_{\mu=0}\Big(\tr(\rho^2) - \lambda^\mu_{max} (\rho) \Big) = \sum^{M-1}_{\mu=0}C_\mu(\rho)$, where, for $\mu=0,\ldots,M-1$, $\lambda^\mu_{max} (\rho)$ is the maximum of the eigenvalues of $A^\mu(\rho)$

with $A^\mu_{ij}(\rho) = \tr [\rho \sigma^\mu_i \rho\sigma^\mu_j]$.

The entanglement distance:

> Given a state $\rho$, we consider all of its possible decomposition $\{p_j,\rho_j\}$, such that $\rho = \sum_j p_j \rho_j$, where $\sum_j p_j = 1$ and $\tr[\rho_j] = 1$.

> where, for each $j$, $U_j^\mu$ is an $SU(2)$ local unitary operator acting on qubit $\mu$.

> $E(\rho) = \inf_{\{p_j,\rho_j\}} \Big\{ \sum_{\mu=1}^{M-1} \inf_{\{U_j^\mu\}} C_\mu\left( \rho^\mu_U(\{p_j,\rho_j,U_j^\mu\}) \right) \Big\}$

The Bell-diagonal claim:

> We were not able to find a simple analytic solution of the minimization procedure for the most general case of BD states. However, numerical minimization provided us with empirical evidence that the procedure (22) also leads for these states to the squared concurrence, as shown in figure \ref{figBD_ED}, which represent a face of the tetrahedral domain of BD states.

The figure plots $E/2$, and for Werner states the paper states $E(\rho_W(p))=2\Theta(1/2-p)(1-2p)^2$, "twice the squared concurrence". The printed sum in Eq. (22) starts at $\mu=1$; the factor 2 matches the sum over both sites of Eq. (QCDrho).

## Verified locator

Source: https://arxiv.org/abs/2205.07143v2
- URL: https://arxiv.org/abs/2205.07143v2 (source `QCDED-V4.tex`, md5 `232776c9cef202cc624a80958cb4c818`):
  - the site QCD, l. 207–230;
  - decompositions and partial rotations, l. 242–264;
  - the entanglement distance, l. 266–269;
  - Bell-diagonal states, l. 349–357;
  - the claim, l. 368;
  - the Werner formula, l. 397–400.
- DOI: 10.1038/s41598-023-29438-7 (https://doi.org/10.1038/s41598-023-29438-7).
