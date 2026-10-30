---
bibkey: acharyakypraiosguta2016lowranktomography
authors: Anirudh Acharya, Theodore Kypraios and Mădălin Guţă
year: 2016
title: "Statistically efficient tomography of low rank states with incomplete measurements"
doi: 10.1088/1367-2630/18/4/043018
url: "https://arxiv.org/abs/1510.03229v2"
claim: "For multiple-ion tomography with Pauli settings, the paper studies the smallest eigenvalue of G^{-1/2} Ī G^{-1/2}, where Ī is the Fisher information averaged over all 3^n settings and G the Frobenius metric of a local parametrisation of rank-r states, and conjectures that for any fixed rank it is bounded below by a constant for all states of rank r and arbitrarily many ions."
strata_touched:
  - D5/S3/Quantum/Tomography/PauliFisherGHZRefutation
license: citation-only
triage: anchor
---

# Acharya, Kypraios and Guţă, Statistically efficient tomography of low rank states with incomplete measurements

A. Acharya, T. Kypraios and M. Guţă, New J. Phys. 18(4), 043018 (2016); arXiv:1510.03229v2. Quotations are from the v2 TeX source.

In multiple-ion tomography of $n$ qubits, a setting $\mathbf s\in\{x,y,z\}^n$ measures each ion in the eigenbasis of the corresponding Pauli matrix, with outcome probabilities $p_\rho(\mathbf o|\mathbf s)=\langle\lambda^{\mathbf s}_{\mathbf o}|\rho|\lambda^{\mathbf s}_{\mathbf o}\rangle$. For a local parametrisation $\rho_\theta$ of rank-$r$ states, $G_{a,b}=\operatorname{Tr}[\partial_a\rho_\theta\,\partial_b\rho_\theta]$ is the Frobenius weight matrix and $I(\rho|\mathbf s)_{a,b}=\sum_{\mathbf o}p^{-1}\partial_ap\,\partial_bp$ the Fisher matrix of one setting; $\bar I$ averages it over all Pauli settings. The paper states:

> While the full dependence of $\lambda_{min}$ on $r$ and $d$ is unclear, we conjecture that for any fixed rank, $\lambda_{min}$ is larger than a fixed constant for all states of rank $r$, of arbitrarily many ions. If this was true, it would imply that a state of fixed rank $r$ can be estimated efficiently with $O(\log d)$ settings.

Here $\lambda_{min}=\lambda_{min}(G^{-1/2}\bar IG^{-1/2})$.

## Verified locator

Source: https://arxiv.org/abs/1510.03229v2
- DOI: https://doi.org/10.1088/1367-2630/18/4/043018 (New Journal of Physics 18(4), 043018, 2016; title, authors, journal, volume, issue and article number from Crossref).
- URL: https://arxiv.org/abs/1510.03229v2. The e-print member `Efficient-Ion-Tomography.tex` has 861 lines and md5 `3d551c60e2cb8bfac911d3ecc1dc781c`. Locations:
  - the measurement model, l. 113–121;
  - the local parametrisation and $G$, l. 157–173;
  - the Fisher matrix of one setting, l. 174–176, and its average over a set of settings, l. 178–181;
  - the average $\bar I$ over all $3^n$ Pauli settings, l. 335;
  - the conjecture, l. 360.
