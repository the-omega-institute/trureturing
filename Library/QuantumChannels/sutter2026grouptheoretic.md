---
bibkey: sutter2026grouptheoretic
authors: Tobias C. Sutter, Christopher Popp and Beatrix C. Hiesmayr
year: 2026
title: "Group-Theoretic Perspective on the PPT and Realignment Criteria in the Magic Simplex for Bipartite Qutrits"
doi: 10.1103/z7jn-4try
url: https://arxiv.org/abs/2508.18393v2
claim: "Section VI states as open whether an entanglement criterion based on the entry-wise 1-norm of the Weyl–Bloch vector can be derived for general bipartite qudits, and reports numerically that separable pure two-qutrit states seem to satisfy ‖β‖₁ ≤ 25 while pure states reach ≈ 25.9735."
strata_touched:
  - D5/S3/Quantum/Entanglement/QutritWeylBlochNormSeparableBound
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1103/z7jn-4try

Source: https://arxiv.org/abs/2508.18393v2

Published in Phys. Rev. A 113, 032440 (2026). Version 2 of the arXiv record (24 March 2026; v1 25 August
2025, titled *A Group-Theoretic Perspective on the PPT and Realignment Entanglement Criteria*) is the
quoted version (`main.tex`); page numbers refer to the v2 PDF. Separability: Section II, p. 2. Weyl
operators, eq. (7): p. 3. Bloch representation, eq. (16): p. 5. Entry-wise 1-norm: p. 6. The open
problem and the numerical observation: Section VI, p. 10.

Separability (p. 2):

> A state $\rho\in\mathcal D(\mathcal H)$ is called separable if it can be written as $\rho=\sum_{i} p_i \, \rho_i^A \otimes \rho_i^B$ for some set $\{p_i , \rho_i^A, \rho_i^B\}$, where $p_i \geq 0$ and $\rho_i^{A/B} \in \mathcal D(\mathcal H_{A/B})$ for all $i$, and $\sum_i p_i =1$; otherwise, $\rho$ is called entangled.

Weyl–Heisenberg operators, eq. (7) (p. 3):

> $W_{k,l} = \sum_{j=0}^{d-1} \omega^{jk} \, |j\rangle\langle j+l|$ where $k,l\in\{0,1,\dots,d-1\}$ and $\omega := e^{\frac{2\pi i}{d}}$, and, throughout this paper, variables taking values in $\{0,1,\dots, d-1\}$ are understood as elements of $\mathbb Z_d$.

Bloch representation, eq. (16) (p. 5):

> any bipartite qudit state can be written as $\rho = \frac{1}{d^2} \sum_{i,j,k,l=0}^{d-1} \beta_{ij,kl} \, W_{i,j} \otimes W_{k,l}$ … Using $\beta_{ij,kl} = \mathrm{tr}\left( \rho \, (W_{i,j}\otimes W_{k,l})^\dagger \right)$ …

The open problem (Section VI, p. 10):

> Going forward, it is furthermore an open problem whether for general bipartite qudit states, an entanglement criterion based on the entry-wise 1-norm of the Bloch vector, similar to Thm. IV.1, can be derived. Ref. [52, 53] present a sufficient criterion for separability, reading $\Vert \beta\Vert_1 \leq 2 \Longrightarrow \rho\in\mathrm{SEP}$ for $\beta$ as in (16), but to the authors' knowledge, no corresponding sufficient entanglement criterion exists. A naive approximation using $\Vert \beta \Vert_1 \leq d^2 \, \Vert \beta \Vert_2$ for $\beta\in\mathbb C^{d^4}$ yields that $\rho$ is entangled if $\Vert\beta\Vert_1 >d^3$. However, the maximal value for pure states $|\psi\rangle\in\mathbb C^d\otimes \mathbb C^d$ is also $\Vert\beta\Vert_1 =d^3$. A quick numerical optimization for $d=3$ yields $\Vert\beta\Vert_1 \lesssim 25.9735$ for general pure states $|\psi\rangle\in\mathbb C^3\otimes\mathbb C^3$, whereas separable pure states seem to satisfy $\Vert \beta\Vert_1 \leq 25$.
