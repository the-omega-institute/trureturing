---
bibkey: huangkosuginishimatsushita2024reflectiondiagonal
authors: Xinchi Huang, Taichi Kosugi, Hirofumi Nishi and Yu-ichiro Matsushita
year: 2024
title: "Optimized Synthesis of Circuits for Diagonal Unitary Matrices with Reflection Symmetry"
doi: 10.7566/JPSJ.93.054002
url: "https://arxiv.org/abs/2310.06676v2"
claim: "Every 2^{2n} x 2^{2n} diagonal unitary whose phases satisfy the reflection symmetry theta(j,j') = theta(2^n-1-j, 2^n-1-j') is realized up to a global phase by an ancilla-free {CNOT, R_z} circuit with 2^{2n-1}+2n-2 CNOT gates; the paper conjectures that this count is optimal in the worst case."
strata_touched:
  - D5/S3/Quantum/Magic/ReflectionDiagonalCNOTLowerBound
license: citation-only
triage: anchor
---

# Huang, Kosugi, Nishi and Matsushita, Optimized Synthesis of Circuits for Diagonal Unitary Matrices with Reflection Symmetry

X. Huang, T. Kosugi, H. Nishi and Y.-i. Matsushita, J. Phys. Soc. Jpn. 93(5), 054002 (2024); arXiv:2310.06676v2. Quotations are from the v2 TeX source.

For $n\ge1$ the paper considers the diagonal unitary $\mathrm D(\boldsymbol\theta)=\operatorname{diag}(e^{\mathrm i\theta_{j,j'}})$ on two $n$-qubit registers whose phases satisfy the reflection symmetry $\theta_{j,j'}=\theta_{2^n-1-j,\,2^n-1-j'}$ (Eq. (1)); in bits this is invariance under complementing all $2n$ bits. Its Algorithm 1 builds an ancilla-free circuit over $\{\mathrm{CNOT},R_z\}$ that realizes $\mathrm D(\boldsymbol\theta)$ up to a global phase with $2^{2n-1}-1$ blocks of one $R_z$ and one CNOT followed by $2n-1$ further CNOT gates, that is $2^{2n-1}+2n-2$ CNOT gates, against $2^{2n}-2$ for general diagonal matrices. The conclusion states:

> Although we conjecture that the number of entanglement gates is at best $2^{2n-1}+2n-2$ in the $\{\mathrm{CNOT}, R_z\}$-based circuit for the worst scenario of diagonal unitary matrices that satisfy Eq. (1), [...]

## Verified locator

Source: https://arxiv.org/abs/2310.06676v2
- DOI: https://doi.org/10.7566/JPSJ.93.054002 (Journal of the Physical Society of Japan 93(5), 054002, 2024; title, authors, journal, volume, issue and article number from Crossref).
- URL: https://arxiv.org/abs/2310.06676v2. The e-print member `main_arXiv2.tex` has 1580 lines and md5 `44a2af1459437b066b4858eed574cd80`. Locations:
  - the gate set $\{\mathrm{CNOT},R_z\}$ and circuits without ancillary qubits, l. 170, 194, 1225;
  - the matrix $\mathrm D(\boldsymbol\theta)$ and the reflection symmetry, Eq. (1), l. 207–227;
  - the CNOT count $2^{2n-1}+2n-2$ of the construction, l. 229, 314;
  - realization up to a global phase, l. 429, 445, 1140;
  - the conjecture, l. 847.
