---
bibkey: seshadrileditzkysiddhusmith2023signalling
authors: Akshay Seshadri; Felix Leditzky; Vikesh Siddhu; Graeme Smith
year: 2023
title: "On the separation of correlation-assisted sum capacities of multiple access channels"
doi: 10.1109/TIT.2023.3274434
url: https://arxiv.org/abs/2205.13538v3
claim: "The paper bounds the classical, quantum-assisted and no-signalling-assisted sum capacities of multiple access channels built from nonlocal games by the games' winning probabilities, introduces the signalling game in which each of two players must guess the other's question, proves that its classical value with uniformly drawn questions is one over the larger question-set size, and, from linear programs for question-set sizes 2 to 10, expects the classical, quantum and no-signalling values of this game to coincide."
strata_touched:
  - D5/S3/Quantum/Information/SignallingGameValueEquality
license: citation-only
triage: anchor
---

# Seshadri, Leditzky, Siddhu and Smith, the signalling game

A. Seshadri, F. Leditzky, V. Siddhu and G. Smith, arXiv:2205.13538v3 [cs.IT] (3 August 2023; v1 26 May 2022); IEEE Trans. Inf. Theory 69 (2023), no. 9, 5805–5844. Quotations are from the v3 TeX source, with cross-references omitted.

Strategies and values (Section 2): for $N$ players with question sets $\mathcal X_i$ and answer sets $\mathcal Y_i$, classical strategies are convex combinations of products $p_{Y_1|X_1}\cdots p_{Y_N|X_N}$, quantum strategies are

> $p_{\bm{Y} | \bm{X}}(y_1, \dotsc, y_N | x_1, \dotsc, x_N) = \tr\left[\rho \left(E^{(x_1)}_{y_1} \otimes \dotsm \otimes E^{(x_N)}_{y_N}\right)\right]$

for a shared state $\rho$ and local POVMs, and no-signalling strategies satisfy $p_{Y_i|\bm X}(y_i|x_1,\dots,x_N)=p_{Y_i|X_i}(y_i|x_i)$. With uniformly drawn questions, $\omega^{\text{cl}}(G)$, $\omega^{\text{Q}}(G)$ and $\omega^{\text{NS}}(G)$ are the maximal winning probabilities over these sets.

The signalling game (Section 3.2.1):

> Formally, we consider question sets $\mathcal{X}_1$, $\mathcal{X}_2$ and answer sets $\mathcal{Y}_1 = \mathcal{X}_2$ and $\mathcal{Y}_2 = \mathcal{X}_1$, and the winning condition is defined as $\mathcal{W} = \{(x_1, x_2, y_1, y_2) \in (\mathcal{X}_1 \times \mathcal{X}_2) \times (\mathcal{Y}_1 \times \mathcal{Y}_2) \mid y_1 = x_2,\ y_2 = x_1\}$.

The paper proves $\omega^{\text{cl}}(G_{\text s})=1/\max(|\mathcal X_1|,|\mathcal X_2|)$ and states:

> For $2 \leq |\mathcal{X}_1|, |\mathcal{X}_2| \leq 10$, we verify that the numerically computed value for $\omega^{\text{NS}}(G_{\text{s}})$ matches $\omega^{\text{cl}}(\mathcal{N}_{G_{\text{s}}}) = 1/\max(|\mathcal{X}_1|, |\mathcal{X}_2|)$. Thus, we expect $\omega^{\text{cl}}(\mathcal{N}_{G_{\text{s}}}) = \omega^{\text{Q}}(\mathcal{N}_{G_{\text{s}}}) = \omega^{\text{NS}}(\mathcal{N}_{G_{\text{s}}})$ for the signalling game.

## Verified locator

Source: https://arxiv.org/abs/2205.13538v3
- DOI: https://doi.org/10.1109/TIT.2023.3274434 (IEEE Trans. Inf. Theory 69 (2023), no. 9, 5805–5844; author list, journal, volume, issue and pages from Crossref).
- URL: https://arxiv.org/abs/2205.13538v3 (the e-print is a gzipped tar archive; member `MAC_bound.tex`, 2474 lines, md5 `29986fdbbc8f9c2343aa03e9feb14484`):
  - classical, quantum and no-signalling strategies, l. 175–196;
  - the uniform-question values $\omega^{\text{cl}}$, $\omega^{\text{Q}}$, $\omega^{\text{NS}}$, l. 198–205;
  - the signalling game, l. 836–844;
  - the classical value, l. 864–876;
  - the numerical check and the expectation, l. 880.
- The arXiv version dates are from the arXiv metadata.
