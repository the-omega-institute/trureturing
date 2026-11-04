---
bibkey: camilolandieliens2019renyissa
authors: Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns
year: 2019
title: "Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states"
doi: 10.1103/PhysRevB.99.045155
url: https://arxiv.org/abs/1810.07070v2
claim: "The paper expresses the Rényi entropies of bosonic and fermionic Gaussian states through the symplectic or covariance eigenvalues, proves subadditivity for all orders (bosons) and for orders up to two (fermions), proves strong subadditivity at order two for bosons, finds numerical violations of strong subadditivity above order two for bosons and above about 1.3 for fermions, and conjectures that strong subadditivity holds for bosonic Gaussian states for orders up to two and for fermionic Gaussian states for orders up to one."
strata_touched:
  - D5/S3/Quantum/Thermal/GaussianRenyiStrongSubadditivity
  - D5/S3/Quantum/Analysis/BosonicRenyiStieltjes
  - D5/S3/Quantum/Analysis/BosonicRenyiStieltjes/PoissonWeight
  - D5/S3/Quantum/Fermionic/GaussianRenyiStrongSubadditivity
  - D5/S3/Quantum/Analysis/FermionicRenyiStieltjes
license: citation-only
triage: anchor
---

# Camilo, Landi and Eliëns, strong subadditivity of Gaussian Rényi entropies

## Verified locator

DOI: https://doi.org/10.1103/PhysRevB.99.045155 (Phys. Rev. B 99, 045155, published 31 January 2019).

Source: https://arxiv.org/abs/1810.07070v2

G. Camilo, G. T. Landi and S. Eliëns, arXiv:1810.07070v2 (the latest version). Quotations are from the v2 TeX source (`RenyiGaussian_v2.tex`).

## Statement

For an $N$-mode bosonic Gaussian state with covariance matrix $\Gamma$ ($\Gamma+i\Omega\ge0$) and symplectic eigenvalues $\sigma_i\ge1$, Eq. `renyi_bosonic_1` gives
$$S_\alpha(\rho)=\frac1{\alpha-1}\sum_{i=1}^N\ln\Big[\Big(\frac{\sigma_i+1}2\Big)^\alpha-\Big(\frac{\sigma_i-1}2\Big)^\alpha\Big],$$
and strong subadditivity is $S_\alpha(\rho_{AB})+S_\alpha(\rho_{BC})-S_\alpha(\rho_{ABC})-S_\alpha(\rho_B)\ge0$ (Eq. `RCMI`). For bosons the source states (Section 4):

> It provides clear evidence that SSA is violated for all $\alpha>2$, while no violation is found for $0\le\alpha\le2$. We conjecture that this result holds true in general.

and for fermions: "Again, we lack a formal proof for SSA to hold for $\alpha \in [0,1]$, but we conjecture it to be true." The final section asks "to prove the conjectured domains of validity of the SSA for the Rényi-$\alpha$ entropies" and suggests Schur-complement techniques. Order two is proved in the source (Hadamard–Fischer) and by Adesso, Girolami and Serafini, Phys. Rev. Lett. 109, 190502 (2012).

## Encoding and boundary

The repository defines the bosonic Gaussian Rényi entropy of a physical covariance matrix through the eigenvalues of $V^{1/2}(i\Omega)V^{1/2}$ (the symplectic eigenvalues with both signs) and proves strong subadditivity over pairwise disjoint mode sets for every order $0<\alpha\le2$, $\alpha\ne1$. The proof writes the entropy as a positive mixture $n c_\alpha+\int_0^1w_\alpha(x)\ln\det(V+ix\Omega)\,dx$ and applies Koteljanskii's classical determinant inequality to the Hermitian positive definite matrices $V+ix\Omega$. For fermions the repository defines the Rényi entropy of a real antisymmetric covariance matrix $\Gamma$ whose Hermitian matrix $i\Gamma$ has spectrum in $[-1,1]$ as half the sum, over all eigenvalues $\lambda$ of $i\Gamma$, of $\frac1{1-\alpha}\ln\big[(\frac{1+\lambda}2)^\alpha+(\frac{1-\lambda}2)^\alpha\big]$ (Eq. `renyi_fermionic_1`), and proves strong subadditivity over pairwise disjoint mode sets for every order $0<\alpha<1$, the conjectured fermionic range without its endpoints. The proof writes the entropy as $n\ln2+\int_0^1v_\alpha(u)\ln\det(I+iu\Gamma)\,du$ with a positive weight $v_\alpha$ and applies the same Koteljanskii inequality to $I+iu\Gamma$. Order one (von Neumann strong subadditivity, Lieb–Ruskai), order zero, the violation halves (bosons above order two, fermions above about $1.3$), fermionic orders in $[1,1.3]$ and non-Gaussian states are outside these conclusions.
