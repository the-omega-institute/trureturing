---
bibkey: hsuetal2026tradingsymmetry
authors: Hsin-Yu Hsu; Gelo Noel M. Tabia; Kai-Siang Chen; Mu-En Liu; Tamás Vértesi; Nicolas Brunner; Yeong-Cherng Liang
year: 2026
title: "Trading symmetry for Hilbert-space dimension in Bell-inequality violation"
doi: 10.1088/2058-9565/ae6bb1
url: https://arxiv.org/abs/2601.02893v4
claim: "The paper asks whether symmetric quantum strategies, with identical measurements on a swap-invariant state, reach the maximal quantum violation of party-permutation-invariant Bell inequalities in the minimal Hilbert-space dimension; it gives a family of identical Fourier-type measurements for the CGLMP inequality, finds Bell inequalities where symmetric strategies in minimal dimension are suboptimal, and conjectures that its symmetric form of the two-setting SATWAP inequalities reaches the maximal quantum value 2(d-1) with these measurements and a symmetric maximally entangled state for every d."
strata_touched:
  - D5/S3/Quantum/Contextuality/SymmetricSatwapMaximalViolation
license: citation-only
triage: anchor
---

# Trading symmetry for Hilbert-space dimension in Bell-inequality violation

H.-Y. Hsu, G. N. M. Tabia, K.-S. Chen, M.-E. Liu, T. Vértesi, N. Brunner and Y.-C. Liang, arXiv:2601.02893v4 (17 June 2026, the published version); Quantum Science and Technology 11(3) (2026), 035003. Quotations are from the v4 TeX source, with the macros `\ketbra` and `\intv{d}` (that is, $[d]$) written out and citations omitted.

Symmetric quantum strategy (Definition `def:Symmetric strategy`): both parties perform the same measurements, $M^{B}_{a|x} = M^{A}_{a|x}$, on a shared state with $\rho_{BA}=\rho_{AB}$, where $\rho_{BA}:=S\rho_{AB}S^{\dagger}$ and $S:=\sum_{ij}|i\rangle\langle j|_A\otimes|j\rangle\langle i|_B$.

The measurements:

> $M_{a|0}^{A} = |a\rangle\langle a|, \quad M_{a|1}^{A} = U|a\rangle\langle a|U^{\dagger},\quad U:=TW,$ … $T:= -1 \bigoplus \mathbb{I}_{d-1}$ and $W:= \sum_{i,j\in[d]}\frac{|i\rangle\langle j|}{d\sin{[(i-j-\frac{1}{2})\frac{\pi}{d}}]}$.

The correlators: $\langle A^k_xB^\ell_y\rangle=\sum_{a,b=0}^{d-1}\omega^{ak+b\ell}P(a,b|x,y)$ with $\omega={\rm e}^{2\pi i/d}$.

The symmetric SATWAP expression:

> $\tilde{\mathcal I}_{d} = \sum_{k = 1}^{d-1} \big[ \omega^{-2k}\big(a_k\langle A_{1}^{-k}B_{1}^{-k}\rangle + a_k^* \langle A_{1}^{-k}B_{2}^{-k}\rangle + a_k^* \langle A_{2}^{-k}B_{1}^{-k}\rangle\big) + \omega^{-3k}a_k\langle A_{2}^{-k}B_{2}^{-k}\rangle\big]$, where $a_k=\frac{(1-i)}{2}\omega^{\frac{k}{4}}$.

The conjecture:

> Our computation results show that for the symmetric inequalities of Eq. (symSATWAP), the measurement of Eq. (CGLMP-Opt), in conjunction with a symmetric maximally entangled two-qudit state, indeed reproduces the maximal quantum violation of $2(d-1)$ for $d\le 100$. Together with the fact that this maximal quantum violation self-tests a maximally entangled two-qudit state, we know that the symmetric family of SATWAP inequalities, Eq. (symSATWAP), also cannot exhibit a trade-off for $d\le 100$. Moreover, we conjecture that this holds true for any higher $d$ as well.

The measurements are labelled by settings $0,1$ and the SATWAP expression by settings $1,2$. For $d=2$ both assignments of the settings reach the value $2$; for $d=3,4,5,8$ the largest eigenvalue of the Bell operator is $2(d-1)$ only when setting $0$ is assigned to setting $1$ (floating-point computation).

## Verified locator

Source: https://arxiv.org/abs/2601.02893v4
- URL: https://arxiv.org/abs/2601.02893v4 (the e-print is a tar archive; member `SymmetricBIV-arXiv_v2.tex`, 2736 lines, md5 `6116dc142244f252c16a835d291626cf`):
  - Definition `def:Symmetric strategy`, l. 285–297;
  - the measurements, Eq. `Eq:CGLMP-Opt`, l. 488–498;
  - the correlators, Eq. `Eq:Correlators:d`, l. 513–519;
  - the symmetric SATWAP expression, Eq. `Eq:symSATWAP`, l. 523–530;
  - the conjecture, l. 532.
- DOI: 10.1088/2058-9565/ae6bb1 (https://doi.org/10.1088/2058-9565/ae6bb1; Crossref lists Quantum Science and Technology, volume 11, issue 3, article 035003, published 5 June 2026).
