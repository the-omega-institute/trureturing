---
bibkey: mukherjeebanerjeesenguptasen2021fragmentation
authors: Bhaskar Mukherjee, Debasish Banerjee, K. Sengupta, Arnab Sen
year: 2021
title: "Minimal model for Hilbert space fragmentation with local constraints"
doi: 10.1103/PhysRevB.104.155117
url: https://arxiv.org/abs/2106.14897v3
claim: "The paper studies a one-dimensional spin-1/2 chain with no two adjacent up spins whose Hamiltonian H_3 flips three-site patterns, exhibits Hilbert space fragmentation with bubble eigenstates built from three-site X and Y units separated by at least two down spins, tabulates their degeneracies for L = 16, 18, 20, and states that it has not found a closed form for these degeneracies for arbitrary L."
strata_touched:
  - D5/S3/Quantum/SpinChains/BubbleEigenstateDegeneracy
license: citation-only
triage: anchor
---

# Mukherjee, Banerjee, Sengupta and Sen, minimal model for Hilbert space fragmentation

## Verified locator

DOI: https://doi.org/10.1103/PhysRevB.104.155117 (Phys. Rev. B 104, 155117, published 11 October 2021).

Source: https://arxiv.org/abs/2106.14897v3

B. Mukherjee, D. Banerjee, K. Sengupta and A. Sen, arXiv:2106.14897v3 (the latest version). Quotations are from the v3 TeX source (`fragmentation_prb_v2.tex`).

## Statement

On a periodic chain of $L$ sites with no two adjacent up spins, the bubble eigenstates of $H_3$ are products of three-site units $X_j=(X_{1,j}+X_{2,j})/\sqrt2$ (energy $+1$) and $Y_j=(X_{1,j}-X_{2,j})/\sqrt2$ (energy $-1$), with $X_{1,j}=\uparrow_{j-1}\downarrow_j\uparrow_{j+1}$ and $X_{2,j}=\downarrow_{j-1}\uparrow_j\downarrow_{j+1}$, all other spins down. The source counts them combinatorially:

> The number of bubble eigenstates at an integer energy $E = n_1 - n_2$ can be calculated for a given system size from the number of configurations that satisfy the hard core constraint of at least two consecutive $\downarrow$ spins separating any of the $n_1$ $X$ and $n_2$ $Y$ units on the periodic one-dimensional lattice.

After tabulating these numbers for $L=16,18,20$ (Table I) it states:

> While we have not been able to find a closed form expression for the degeneracy of the different bubble eigenstates for an arbitrary $L$, we can still place a lower bound on the degeneracy of such states when $L \gg 1$.

## Encoding and boundary

The repository counts pairs of a set of unit centres on the cycle of $L$ sites, any two at cyclic distance at least $5$, and a subset of centres labelled $X$, by energy $\#X-\#Y$, and proves for every $L\ge5$ the closed form $[E=0]+\sum_{n=1}^{\lfloor L/5\rfloor}\frac Ln\binom{L-4n-1}{n-1}\binom n{(n+E)/2}$, where the label factor $\binom n{(n+E)/2}$ is $0$ unless $n+E$ is even and $|E|\le n$. The step counting admissible $n$-element centre sets is a classical cyclic placement count (marked gaps reduced to compositions). The eigenstate property of the bubble states under $H_3$, the remaining eigenstates of $H_3$, the asymptotic bound and open boundary conditions are outside this conclusion.
