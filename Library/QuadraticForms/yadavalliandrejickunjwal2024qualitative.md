---
bibkey: yadavalliandrejickunjwal2024qualitative
authors: Shiv Akshar Yadavalli; Nikola Andrejic; Ravi Kunjwal
year: 2024
title: "Qualitative equivalence between incompatibility and Bell nonlocality"
doi: 10.1103/PhysRevA.110.L060201
url: https://arxiv.org/abs/2008.10100v3
claim: "The paper shows that every non-trivial joint measurability structure with finitely many vertices has a quantum realization by measurements that enable a Bell violation, so a non-trivial structure is necessary and sufficient for a Bell violation. Its Supplemental Material studies trine qubit measurements with a purity parameter and a common bias. For the first family it states the pairwise joint-measurability condition from earlier work, computes the triplewise threshold numerically by a semidefinite program, and conjectures that threshold to be the piecewise function 1+b, 2/3, 1-b."
strata_touched:
  - D5/S3/Quantum/Measurement/BiasedTrineJointMeasurabilityThreshold
license: citation-only
triage: anchor
---

# Yadavalli, Andrejic and Kunjwal, incompatibility and Bell nonlocality

S. A. Yadavalli, N. Andrejic and R. Kunjwal, arXiv:2008.10100v3 [quant-ph]; Phys. Rev. A 110, L060201 (2024). Quotations are from the v3 Supplemental Material TeX.

The trine directions are $\vec n_k=\cos\frac{2k\pi}{3}\vec e_x+\sin\frac{2k\pi}{3}\vec e_z$, $k\in\{1,2,3\}$. With a global purity parameter $\eta\in[0,1]$ and a bias $b\in[-1,1]$ such that $|b|\le1-\eta$, the first family is

$$E_k(x_k)=\frac{1}{2}\left((1+x_k b)I+\eta x_k\vec{n}_k\cdot\vec{\sigma}\right),\qquad x_k\in\{-1,+1\}.$$

Citing earlier work, the source states that the set is pairwise jointly measurable if and only if $\eta\le1+b$ for $b<-\frac13$, $\eta\le\sqrt{3-2b^2}-1$ for $|b|\le\frac13$, and $\eta\le1-b$ for $b>\frac13$. The triplewise threshold $\eta_1^{(3)}(b)$, defined by "the set is triplewise jointly measurable iff $\eta\leq\eta_1^{(3)}(b)$", is obtained by a semidefinite program on a discretization of $b$. The authors write:

> Based on our numerical evaluation and visual inspection, we conjecture the exact form of $\eta_1^{(3)}(b)$ to be
> $$\eta_1^{(3)}(b)=\begin{cases}1+b, & -1\leq b<-\frac{1}{3},\\ \frac{2}{3}, & b\in\left[-\frac{1}{3},\frac{1}{3}\right],\\ 1-b, & \frac{1}{3}< b\leq 1.\end{cases}$$

## Verified locator

Source: https://arxiv.org/abs/2008.10100v3
- DOI: https://doi.org/10.1103/PhysRevA.110.L060201 (Phys. Rev. A 110, L060201 (2024); author list, journal, volume, issue and article number from Crossref).
- URL: https://arxiv.org/abs/2008.10100v3. The e-print is a gzipped tar archive; its member `qualequiv_supp_arxiv.tex` has 258 lines and md5 `99ad6f21ee4fb05ae64c577ed2d1efef`. Locations:
  - the trine directions, the domain and the two biased families, l. 112–121;
  - the pairwise condition, the triplewise threshold definition and the conjecture (Example 1), l. 133–164.
- The arXiv versions (v1 23 August 2020, v3 20 November 2024) are from the arXiv metadata.
