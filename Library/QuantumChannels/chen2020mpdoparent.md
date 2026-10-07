---
bibkey: chen2020mpdoparent
authors: Chi-Fang Chen, Kohtaro Kato and Fernando G. S. L. Brandão
year: 2020
title: "Matrix Product Density Operators: when do they have a local parent Hamiltonian?"
doi: null
url: https://arxiv.org/abs/2010.14682v3
claim: "Conjecture III.1 asserts a uniform completely contractive data-processing bound for conditional mutual information under every channel with scalar whole-space correctable algebra."
strata_touched:
  - D5/S3/Quantum/Information/ChenKatoBrandaoCMIRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: null

Source: https://arxiv.org/abs/2010.14682v3

The arXiv abstract page lists the arXiv-issued DOI
https://doi.org/10.48550/arXiv.2010.14682 and no published journal DOI.
Version 3 is the source version. Section II.D, PDF p. 11, equation (22)
defines the correctable algebra. Section III.C, PDF p. 16, contains
Proposition III.3 and Conjecture III.1; Proposition III.4 follows on p. 17.

The correctable-algebra definition reads:

> For a given channel $\mathcal{E}:A\to A'$, we define the correctable algebra
> $\mathcal{A}(\mathcal{E})\subset\mathcal{B}(\mathcal{H}_A)$ as
> $\mathcal{A}(\mathcal{E}):=\mathrm{Alg}\{O_A\mid[O_A,E_a^\dagger E_b]=0,\ \forall a,b\}$.

Conjecture III.1 reads:

> For any channel $\mathcal{E}:C\rightarrow C'$ with trivial correctable algebra
> $\mathcal{A}(\mathcal{E})=\mathbb{C}I$, there exists a constant $\eta<1$ such that
> for any tripartite system $ABC$ and any state $\rho_{ABC}$, it holds that
> $I(A:C'|B)_{\mathcal{E}(\rho)}\le\eta I(A:C|B)_\rho$.

Proposition III.3 reads:

> Let $\mathcal{E}:C\to C'$ be a CPTP map which has trivial correctable algebra.
> Consider a tripartite system $A\otimes B\otimes C$. Then, for any state
> $\rho_{ABC}$ with $I(A:C|B)_\rho>0$, we have
> $I(A:C'|B)_{\mathcal{E}(\rho)}<I(A:C|B)_\rho$.

Section I, PDF p. 3, equation (1) reads:

> The CMI $I(A:C|B)_\rho$ is a function defined for a tripartite state
> $\rho_{ABC}$ as
> $I(A:C|B)_\rho=S(AB)_\rho+S(BC)_\rho-S(B)_\rho-S(ABC)_\rho$,
> where $S(A)_\rho=-\mathrm{tr}\rho_A\log_2\rho_A$ is the von Neumann entropy of
> the reduced state on $A$.

The source's Proposition III.4 is conditional on Conjecture III.1. A
refutation of that conjecture removes this route to unconditional decay;
it does not refute exponential decay for every Y-shaped MPDO.

Bény, Kempf and Kribs, *Quantum Error Correction of Observables*,
https://arxiv.org/abs/0705.1574, DOI https://doi.org/10.1103/PhysRevA.76.042303,
Theorem 9, supplies
the support-sensitive criterion $[P E_a^\dagger E_b P,O]=0$ for correctability
on a projected support. The support projection $P$ is part of that
criterion; a correctable observable on a chosen support need not be
correctable on the whole input space. This distinguishes recovery of
selected preparations from the whole-space algebra in equation (22).
