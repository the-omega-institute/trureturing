---
bibkey: movahedi2025diminishedsombor
authors: F. Movahedi
year: 2025
title: "Diminished Sombor matrix, spectral radius, and energy of the graphs"
doi: 10.48550/arXiv.2508.06531
url: https://arxiv.org/abs/2508.06531v1
claim: "There does not exist a graph whose diminished Sombor energy is an integer value."
strata_touched:
  - D5/S3/Combinatorics/Graph/DiminishedSomborEnergyRefutation
license: citation-only
triage: anchor
---

# Diminished Sombor energy

## Verified locator

DOI: 10.48550/arXiv.2508.06531

Source: https://arxiv.org/abs/2508.06531v1

The matrix and energy definitions are on page 2. Conjecture 5.1 is in Section 5, page 19.

## Definitions

Page 2: "Motivated by this newly introduced index, and following on the approach in [5, 28], we introduce the diminished Sombor matrix for the graph G, denoted by ℳ = M_DS(G) = (μ_ij), of order n as follows"

For a finite simple graph with vertex degrees $d_i$,

$$
\mu_{ij}=\begin{cases}
\dfrac{\sqrt{d_i^2+d_j^2}}{d_i+d_j}&\text{if }v_iv_j\in E,\\
0&\text{otherwise}.
\end{cases}
$$

Page 2: "We define the diminished Sombor energy as follows"

$$E_{DSO}(G)=\sum_{i=1}^{n}|\lambda_i|,$$

where the $\lambda_i$ are the real eigenvalues of $M_{DS}(G)$, counted with multiplicity.

## Conjecture 5.1

Section 5, page 19: "There does not exist a graph whose diminished Sombor energy is an integer value."

The graph domain includes edgeless graphs: Corollary 4.3, page 17, lists $\overline{K_n}$ as an equality case in the upper energy bound. On an edgeless graph the non-edge branch makes every matrix entry zero. Its eigenvalues and energy are therefore zero, an integer. This refutes the literal conjecture; the restriction to graphs with at least one edge remains open.
