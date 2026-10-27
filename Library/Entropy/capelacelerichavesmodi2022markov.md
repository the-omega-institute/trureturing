---
bibkey: capelacelerichavesmodi2022markov
authors: Matheus Capela; Lucas C. Céleri; Rafael Chaves; Kavan Modi
year: 2022
title: "Quantum Markov monogamy inequalities"
doi: 10.1103/PhysRevA.106.022218
url: https://arxiv.org/abs/2108.11533v4
claim: "The paper proves a monogamy inequality for coherent information in four-time quantum Markov processes, gives six- and eight-time inequalities, and conjectures that for every Markov chain X_n to X_1 to Y_1 to Y_n and every permutation f the diagonal sum of the mutual informations I(X_i:Y_i) dominates the permuted sum, classically (Conjecture 1, checked for n up to 4) and with coherent information quantumly (Conjecture 2)."
strata_touched:
  - D5/S3/Entropy/MarkovMonogamyPermutationInequality
license: citation-only
triage: anchor
---

# Capela, Céleri, Chaves and Modi, quantum Markov monogamy inequalities

M. Capela, L. C. Céleri, R. Chaves and K. Modi, arXiv:2108.11533v4 [quant-ph] (1 July 2022; v1 26 August 2021); Phys. Rev. A 106, 022218 (2022). Quotations are from the v4 TeX source, with cross-references omitted.

Markov processes and mutual information (Section II): a discrete process is a joint law $p(x_1,\dots,x_n)$, Markovian when

> $p(x_{i}\vert x_{i-1},\dots,x_{1})=p(x_{i} \vert x_{i-1}) \quad \forall i$,

with $H(X)=-\sum_xp(x)\log p(x)$ and $I(X_i:X_j)=H(X_i)+H(X_j)-H(X_i,X_j)$.

The classical conjecture (Conjecture 1):

> Consider the Markovian process $X_n \rightarrow \cdots \rightarrow X_1 \rightarrow Y_1 \rightarrow \cdots \rightarrow Y_n$. The variables $X_1$ and $Y_1$ are to be interpreted as input and output of a given channel, respectively. The variables $X_i$ and $Y_i$, with $i=2,\dots,n$, are interpreted as pre-processed and post-processed variables, respectively. Then for any bijective function $f \colon \{1,\dots,n\} \rightarrow \{1,\dots,n\}$, it holds that $\sum_{i=1}^{n} I(X_i:Y_i) \geq \sum_{i=1}^{n} I(X_i:Y_{f(i)})$, where $I(X:Y)$ denotes the mutual information of random variables $X$ and $Y$.

> The conjecture above has been checked for $n$ up to 4, that is, Markov chains with 8 random variables.

The quantum four-time inequality (Theorem 1) states, for a state $\rho_1$ and channels $\Lambda_1,\Lambda_2,\Lambda_3$, $I_c(\rho_1,\Lambda_3\circ\Lambda_2\circ\Lambda_1)+I_c(\Lambda_1(\rho_1),\Lambda_2)\ge I_c(\rho_1,\Lambda_2\circ\Lambda_1)+I_c(\Lambda_1(\rho_1),\Lambda_3\circ\Lambda_2)$, and Conjecture 2 states the permutation inequality for coherent information along a quantum Markov process.

## Verified locator

Source: https://arxiv.org/abs/2108.11533v4
- DOI: https://doi.org/10.1103/PhysRevA.106.022218 (Phys. Rev. A 106, 022218 (2022); author list, journal, volume and article number from Crossref).
- URL: https://arxiv.org/abs/2108.11533v4 (the e-print is a gzipped tar archive; member `PRA-v1.tex`, 1112 lines, md5 `536c7b7e54c94f79fad588afe7cf5fa5`):
  - Markov processes, entropy and mutual information, l. 118–145;
  - Conjecture 1, l. 153–159, and the check for $n\le4$, l. 161;
  - Theorem 1 (quantum four-time inequality), l. 271–278;
  - Conjecture 2, l. 445–454.
- The author list and the arXiv dates are from the arXiv metadata.
