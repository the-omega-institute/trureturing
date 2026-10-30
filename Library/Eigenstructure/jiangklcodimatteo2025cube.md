---
bibkey: jiangklcodimatteo2025cube
authors: Jacky Jiang; Natalie Klco; Olivia Di Matteo
year: 2025
title: "Non-Abelian dynamics on a cube: Improving quantum compilation through qudit-based simulations"
doi: 10.1103/rrmd-fqx6
url: https://arxiv.org/abs/2506.10945v1
claim: "For multi-controlled qudit rotations the rotation angles are transformed by θ = Mβ with M_ij = Π_l (−1)^{f(b_l^(i), g_l^(j))}, f(b,g) = 1 exactly when 0 < b ≤ g; the paper conjectures that its implementation yields an invertible M when the control sequence is a Cartesian product Z_{d1} × ··· × Z_{dk}."
strata_touched:
  - D5/S3/Quantum/Matrix/CartesianControlAngleMatrixInvertible
license: citation-only
triage: anchor
---

# Jiang, Klco and Di Matteo, Non-Abelian dynamics on a cube: improving quantum compilation through qudit-based simulations

J. Jiang, N. Klco and O. Di Matteo, Phys. Rev. D 112, 074512 (2025); arXiv:2506.10945v1. Quotations are from the v1 TeX source.

For a uniformly controlled qudit rotation the angles satisfy $\boldsymbol\theta=M\boldsymbol\beta$ with $M_{ij}=\prod_l(-1)^{f(b^{(i)}_l,g^{(j)}_l)}$, where $f(b,g)=1$ if $0<b\le g$ and $0$ otherwise, and $b^{(i)}$, $g^{(j)}$ are control words from a $d$-ary and a Gray sequencer. For restricted control sequences the paper states:

> By keeping $\boldsymbol C$ general, we sacrifice the guarantee that the matrix $M$ is invertible, although we conjecture our particular implementation yields an invertible $M$ when $\{\boldsymbol C\}=\mathbb Z_{d_1}\times\mathbb Z_{d_2}\times\cdots\times\mathbb Z_{d_k}$, i.e., uniform control but non-uniform qudit dimension.

## Verified locator

Source: https://arxiv.org/abs/2506.10945v1
- DOI: https://doi.org/10.1103/rrmd-fqx6 (Physical Review D 112(7), article 074512; title, authors, journal, volume, issue and article number from Crossref).
- URL: https://arxiv.org/abs/2506.10945v1. E-print members used: `subsec_3a_uniform-rotations.tex` (Eq. (5), l. 38–49), `subsec_3c_restricted-rotations.tex` (53 lines, md5 `f0c01ce3e234380b4ff873056ad98ce7`; the conjecture, l. 38–46) and `app_3c_sequencers.tex` (41 lines, md5 `f7686d5a3486a7b947e2dbe62a9be994`; the sequencers, l. 4–41).
