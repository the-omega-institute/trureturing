---
bibkey: alikhanighanbaridehghanizadeh2024ellipticsombor
authors: Saeid Alikhani, Nima Ghanbari, Mohammad Ali Dehghanizadeh
year: 2024
title: "Elliptic Sombor energy of a graph"
doi: 10.48550/arXiv.2404.18622
url: https://arxiv.org/abs/2404.18622v1
claim: "There is no graph with integer-valued elliptic Sombor energy."
strata_touched:
  - D5/S3/Combinatorics/Graph/EllipticSomborEnergyIntegerRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2404.18622

Source: https://arxiv.org/abs/2404.18622v1

Conjecture 3.9, page 12: "There is no graph with integer-valued elliptic Sombor energy."

The abstract, page 1, defines the matrix and energy:

> Let G be a simple graph with vertex set V(G) = {v₁, v₂, …, vₙ}. The elliptic
> Sombor matrix of G, denoted by A_ESO(G), is defined as the n×n matrix whose
> (i,j)-entry is (dᵢ+dⱼ)√(dᵢ²+dⱼ²) if vᵢ and vⱼ are adjacent and 0 for another cases.

> The elliptic Sombor energy E_ESO of G is the sum of absolute values of the
> eigenvalues of A_ESO(G).

Section 1, page 1, defines dᵢ as the number of vertices adjacent to vᵢ. The matrix
is real and symmetric. Its characteristic-polynomial roots are counted with
algebraic multiplicity when computing the energy.

Two copies of the four-cycle sharing one vertex give a seven-vertex graph with
degrees 4, 2, 2, 2, 2, 2, 2. Its elliptic Sombor matrix has eigenvalues −56, −16,
0, 0, 0, 16, 56 and energy 144. This refutes Conjecture 3.9; it does not alter
the paper's separately established formulas for its listed graph classes.
