---
bibkey: ghanbari2022somborenergy
authors: Nima Ghanbari
year: 2022
title: "On the Sombor characteristic polynomial and Sombor energy of a graph"
doi: 10.1007/s40314-022-01957-5
url: https://arxiv.org/abs/2108.08552v1
claim: "There is no graph with integer-valued Sombor energy."
strata_touched:
  - D5/S3/Combinatorics/Graph/SomborEnergyIntegerRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1007/s40314-022-01957-5

Source: https://arxiv.org/abs/2108.08552v1

Conjecture 3.8, page 13 of the arXiv v1 PDF: "There is no graph with integer-valued Sombor energy."

The Abstract, page 1, defines the Sombor matrix by the following sentence:
"Let G be a simple graph with vertex set V(G) = {v₁, v₂, …, vₙ}. The Sombor matrix of G, denoted by A_SO(G), is defined as the n×n matrix whose (i,j)-entry is √(dᵢ²+dⱼ²) if vᵢ and vⱼ are adjacent and 0 for another cases."
It defines the energy as follows: "The Sombor energy En_SO of G is the sum of absolute values of the eigenvalues of A_SO(G)."
Section 1 restricts graphs to finite simple graphs without directed, multiple or weighted edges or self-loops, and defines degree as the number of adjacent vertices.

The settling module uses this literal matrix and sums the absolute values of its Hermitian eigenvalues inline. Three copies of C₄ sharing one vertex give ten vertices, central degree six and all other degrees two. The module's result refutes Conjecture 3.8 by proving that this graph has energy 48.
