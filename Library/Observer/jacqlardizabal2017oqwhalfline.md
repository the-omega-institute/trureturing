---
bibkey: jacqlardizabal2017oqwhalfline
authors: Thomas S. Jacq; Carlos F. Lardizabal
year: 2017
title: "Open Quantum Random Walks on the Half-Line: The Karlin–McGregor Formula, Path Counting and Foster's Theorem"
doi: 10.1007/s10955-017-1876-x
url: "https://arxiv.org/abs/1701.08400v3"
claim: "For the gambler's-ruin open quantum random walk on {0,...,M} induced by matrices L, R with L*L+R*R=I, the paper computes absorption probabilities and mean hitting times through first-visit generating functions, and conjectures that for every such pair the mean hitting time has the form 1+h(M,M-k)ρ11+h(M,k)ρ22+j(M,k)Re(ρ12) with j(M,k)=-j(M,M-k)."
strata_touched:
  - D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation
license: citation-only
triage: anchor
---

# Jacq and Lardizabal, Open quantum random walks on the half-line

T. S. Jacq and C. F. Lardizabal, J. Stat. Phys. 169(3), 547–594 (2017); arXiv:1701.08400v3. Quotations are from the v3 TeX source.

An open quantum random walk on the half-line has transition matrices $B_i^j$ with $\sum_jB_i^{j*}B_i^j=I$; from $\rho_i\otimes|i\rangle\langle i|$ it moves to $|j\rangle$ with probability $\mathrm{Tr}(B_i^j\rho_iB_i^{j*})$, and the state becomes $B_i^j\rho_iB_i^{j*}/\mathrm{Tr}(B_i^j\rho_iB_i^{j*})\otimes|j\rangle\langle j|$. The nearest-neighbour walk of a pair $L,R$ with $L^*L+R^*R=I$ has $B_i^{i+1}=R$ and $B_i^{i-1}=L$. On the vertices $\{0,\dots,M\}$, starting from $\rho\otimes|k\rangle\langle k|$, $\tau$ is the time to reach $0$ or $M$ and $E_{k,\rho}(\tau)$ its expectation. After examples, Remark 5.3 states:

> Numerical experiments allows us to recognize a behavior that such OQW has in common with Example 5.1, namely, that the mean hitting time has the form
> $$E_{k,\rho}(\tau)=1+h(M,M-k)\rho_{11}+h(M,k)\rho_{22}+j(M,k)Re(\rho_{12}),$$
> where $h, j$ are functions of $M$ and $k=1,\dots, M-1$, with $j$ being a function satisfying $j(M,k)=-j(M,M-k)$. We conjecture that this holds for the gambler's ruin problem associated to *every* pair or matrices $L$, $R$ with $L^*L+R^*R=I$ inducing an OQW on vertices $\{0,\dots,M\}$. A proof of this statement is, up to our knowledge, unknown.

## Verified locator

Source: https://arxiv.org/abs/1701.08400v3
- DOI: https://doi.org/10.1007/s10955-017-1876-x (Journal of Statistical Physics 169(3), 547–594; title, authors, journal, volume, issue and pages from Crossref).
- URL: https://arxiv.org/abs/1701.08400v3. The e-print member `JL_rev2.tex` has 2213 lines and md5 `14ebf963591a84376ea4c598ae5fc1fc`. Locations:
  - the open quantum random walk and its transition rule, l. 77–83; the nearest-neighbour pair $B_i^{i+1}=R$, $B_i^{i-1}=L$, Figure 1 caption, l. 120;
  - the gambler's ruin and the mean hitting time, Theorem 1.7, l. 304–318, and the first-visit functions, l. 1081–1097;
  - the conjecture, Remark 5.3, l. 1291–1293.
