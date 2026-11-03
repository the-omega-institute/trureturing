---
bibkey: liuetal2026parentlindbladians
authors: Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac
year: 2026
title: "Parent Lindbladians for matrix product density operators"
doi: 10.1103/1qyd-59z7
url: "https://arxiv.org/abs/2501.10552v2"
claim: "Parent Lindbladians are built from renormalization channels of matrix product density operators; for the CZX example the four-site channel E = T∘S and the Lindbladian L = Σ_i (E_{2i-1} − 1) on a ring of N qubits are given, and the paper conjectures that the steady state reached from (1+σ_x^{⊗N})/2^N is (1 + 2^{1−N/2} U_CZX)/2^N for every even N, verified numerically for N = 4, 6, 8."
strata_touched:
  - D5/S3/Quantum/TensorNetworks/CZXParentLindbladianSteadyState
license: citation-only
triage: anchor
---

# Liu, Ruiz-de-Alarcón, Styliaris, Sun, Pérez-García and Cirac, Parent Lindbladians for matrix product density operators

Y. Liu, A. Ruiz-de-Alarcón, G. Styliaris, X.-Q. Sun, D. Pérez-García and J. I. Cirac, Phys. Rev. Research 8(1), 013210 (2026); arXiv:2501.10552v2. Quotations are from the v2 TeX source, with the macro `\bo` rendered as $\mathbb 1$; the published version retains the conjecture after its Eq. (F13).

For a ring of $N$ qubits with $N$ even, $U^{(N)}_{CZX}=\prod_iCZ_{i,i+1}\prod_i(\sigma_x)_i$. The CZX example builds renormalization channels $\mathcal T$ (two sites to four) and $\mathcal S$ (four sites to two) from a $4\times4$ permutation $U$, a $16\times16$ signed permutation $V$, block projections $P_\lambda,P'_\lambda$, the weights $\nu_\lambda/m_\lambda$ and a partial trace; $\mathcal E=\mathcal T\circ\mathcal S$ acts on four consecutive sites, $\mathcal E_i$ is its translate to sites $i,\dots,i+3$, and $\mathcal L^{(N)}=\sum_{i=1}^{N/2}(\mathcal E_{2i-1}-\mathbb 1)$. Appendix F states:

> Starting from a trivial state $\rho=\frac{1}{2^N}(\mathbb 1^{\otimes N}+\sigma_x^{\otimes N})$, we numerically verify that: when $N=4,6,8$, the resulting steady state is $\rho_\infty^{(N)}=\frac{1}{2^N}(\mathbb 1_2^{\otimes N}+\frac{1}{2^{N/2-1}}U_{CZX}^{(N)})$. We conjecture that this relation holds for general $N$.

## Verified locator

Source: https://arxiv.org/abs/2501.10552v2
- DOI: https://doi.org/10.1103/1qyd-59z7 (Physical Review Research 8(1), 013210; title, authors, journal, volume, issue and article number from Crossref).
- URL: https://arxiv.org/abs/2501.10552v2. The e-print member `main.tex` has 5296 lines and md5 `c36a5f20f9e3845ecacaa329b8dc5585`. Locations:
  - $U^{(N)}_{CZX}$, l. 3088–3093; the renormalization channels, Example VI.6, l. 3129–3164;
  - $U$, l. 4858–4862; $\mu_\lambda$, l. 4870; $\nu_\lambda$ and $m_\lambda$, l. 4930; the entries of $V$, l. 4933–4936;
  - $\mathcal E$, $\mathcal E_i$, $\mathcal L_i$ and $\mathcal L^{(N)}$, l. 4951–4952;
  - the conjecture, Appendix F, l. 5038–5042.
