---
bibkey: zhangxiang2017averageentropyorbit
authors: Lin Zhang and Hua Xiang
year: 2017
title: "Average entropy of a subsystem over a global unitary orbit of a mixed bipartite state"
doi: 10.1007/s11128-017-1570-6
url: "https://arxiv.org/abs/1509.00211v3"
claim: "For a mixed bipartite state rho_AB and U distributed by Haar measure on the global unitary group, the paper bounds the Haar average of the subsystem von Neumann entropy S(rho'_A), computes the average linear entropy exactly, and asks, as an open problem for the balanced case d_A = d_B, for a proof that the Haar averages of S(rho'_A) and S(rho'_B) coincide."
strata_touched:
  - D5/S3/Quantum/RandomCircuits/BalancedOrbitMarginalEntropy
license: citation-only
triage: anchor
---

# Zhang and Xiang, Average entropy of a subsystem over a global unitary orbit of a mixed bipartite state

L. Zhang and H. Xiang, Quantum Inf. Process. 16(5), 112 (2017); arXiv:1509.00211v3. Quotations are from the v3 TeX source.

For a bipartite state $\rho_{AB}$ on $\mathbb C^{d_A}\otimes\mathbb C^{d_B}$, the paper takes $\rho'_{AB}=U\rho_{AB}U^\dagger$ with $U$ distributed by the normalized Haar measure $\mu$ on $\mathrm U(d_Ad_B)$, writes $\rho'_A=\operatorname{Tr}_B\rho'_{AB}$ and $\rho'_B=\operatorname{Tr}_A\rho'_{AB}$, and studies $\int S(\rho'_A)\,d\mu(U)$ for the von Neumann entropy $S(\rho)=-\operatorname{Tr}(\rho\ln\rho)$. Its closing remarks state:

> Finally, we conclude this section with two open problems: (i) computing the average coherence (via relative entropy of coherence) of a subsystem of isospectral bipartite systems […] and (ii) proving the following identity for the balanced system, i.e., $d_A=d_B$,
> $$\int\mathrm S(\rho'_A)\,d\mu(U)=\int\mathrm S(\rho'_B)\,d\mu(U).$$

The text adds that this identity, with the paper's Theorems A1 and A2, would give two-sided bounds on $\int S(\rho'_A)\,d\mu(U)$ alone.

## Verified locator

Source: https://arxiv.org/abs/1509.00211v3
- DOI: https://doi.org/10.1007/s11128-017-1570-6 (Quantum Information Processing 16(5), 112, 2017; title, authors, journal, volume, issue and article number from Crossref).
- URL: https://arxiv.org/abs/1509.00211v3. The e-print member `QINP-D-16-00527-revision.tex` has 1745 lines and md5 `946d8528bb4ce08e68964aa73d332b78`. Locations:
  - the balanced-case bound on the sum of the two averages, l. 672–687;
  - the two open problems, l. 910–920;
  - the consequence of item (ii), l. 921–927.
