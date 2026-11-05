---
bibkey: monbroussouetal2025hammingweight
authors: Léo Monbroussou; Eliott Z. Mamon; Jonas Landman; Alex B. Grilo; Romain Kukla; Elham Kashefi
year: 2025
title: "Trainability and Expressivity of Hamming-Weight Preserving Quantum Circuits for Machine Learning"
doi: 10.22331/q-2025-05-15-1745
url: https://arxiv.org/abs/2309.15547v4
claim: "The paper studies Hamming-weight preserving variational circuits of RBS/FBS gates, reduces their gradient variance to a product T = T_J ... T_1 of column-stochastic matrices obtained by squaring the gate entries at angle pi/4 in the weight-k subspace, and conjectures that for connected gate patterns with polynomially many gates and fixed weight k the spectral gap 1 - |lambda_2(T_n)| is at least inverse-polynomial in n."
strata_touched:
  - D5/S3/Quantum/RandomCircuits/HammingWeightPatternSpectralGap
license: citation-only
triage: anchor
---

# Monbroussou et al., trainability of Hamming-weight preserving circuits

L. Monbroussou, E. Z. Mamon, J. Landman, A. B. Grilo, R. Kukla and E. Kashefi, Quantum 9, 1745 (2025), DOI 10.22331/q-2025-05-15-1745; arXiv:2309.15547v4 (13 May 2025). Quotations are from the v4 TeX source, with cross-references omitted and `\bm{\theta}` written as $\boldsymbol\theta$.

The stochastic matrices:

> $T_{\lambda}$ is defined as the $d_k \times d_k$ column-stochastic matrix that is constructed by taking the VQC's $\lambda^{\text{th}}$ RBS/FBS unitary is (in the subspace $k$) and replacing its $\pm \cos(\theta_i)$ and $\pm \sin(\theta_i)$ entries with $1/2$.

> $\Big(T_\lambda\Big)_{a,b} := \Big(U_{\lambda}(\theta_\lambda:=\pi/4)\Big)_{a,b}^2$ … $T := T_J \cdots T_2 \cdot T_1$

The spectral gap:

> we will usually denote by $\Delta:=1-|\lambda_2|$ this gap for the stochastic-matrix $T$, which we will refer to as the *spectral gap* of $T$.

Connected patterns:

> The pattern $U_0$ of RBS/FBS gates is said to be *connected* if its associated directed graph $\Gamma(U_0)$ is strongly-connected.

Here $\Gamma(U_0)$ has the qubits as vertices and the gate positions $(i_1,j_1),\dots,(i_J,j_J)$ as edges, "adding arrow tips on each side of every vertical line that represented a gate".

The conjecture (the source leaves its proof "for future work"):

> Let $(U_{0,n})_{n\geq2}$ be a sequence of connected patterns of RBS/FBS gates, where each $U_{0,n}$ is such a pattern over $n$ qubits. If the number $J_n$ of gates in the pattern $U_{0,n}$ satisfies $J_n \in \mathcal{O}\left(\mathrm{poly}(n)\right)$, then for any fixed Hamming weight $k \in \mathcal{O}(1)$, the associated $d_{k,n} \times d_{k,n}$ stochastic matrix $T_n:=T^{(U_{0,n}^k)}$ satisfies $\Delta_n \in \Omega\left(1/\mathrm{poly}(n)\right)$, where $\Delta_n:=1-|\lambda_2(T_n)|$ denotes the spectral gap of the stochastic matrix $T_n$.

## Verified locator

DOI: https://doi.org/10.22331/q-2025-05-15-1745 (Quantum 9, 1745 (2025); the journal text was not compared line by line with v4).

Source: https://arxiv.org/abs/2309.15547v4
- URL: https://arxiv.org/abs/2309.15547v4 (the e-print is a tar archive; member `Quantum.tex`, 2252 lines, md5 `057c1aeb9e7f5c3b57445d20f924f4fc`):
  - the RBS and FBS gates, l. 158–192;
  - the spectral gap, l. 1397–1405;
  - the stochastic matrices $T_\lambda$, l. 1450–1458, and $T$, Eq. `eq:stochastic-matrix-T-def`, l. 1487–1489;
  - connected patterns, Definition `def:connected-pattern`, l. 1631–1640;
  - the conjecture, Conjecture `conj:spectral-gap`, l. 1975–1986.
- The author list, the journal reference and the DOI are from Crossref.
