---
slug: sason-et-al-2025-corona-normalized-laplacian-question-5-21
bibkey: sasonkrupnikhamudberman2025spectraldetermination
doi: 10.3390/math13040549
url: https://arxiv.org/abs/2412.20775v6
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/ClosedNeighborhoodCorona/NormalizedLaplacian.normalized_laplacian_charpoly_corona
---

# Sason et al., Question 5.21

## Problem

> Are the irregular graphs in Theorem 5.20 also cospectral with respect to the normalized Laplacian matrix?

Theorem 5.20 uses adjacency-cospectral regular graphs \(G_1,G_2\) and an arbitrary graph \(H\). It compares \(G_1\diamond H\) with \(G_2\diamond H\) and \(H\diamond G_1\) with \(H\diamond G_2\), where \(\diamond\) is the closed-neighborhood corona. [Theorem 5.20](https://arxiv.org/html/2412.20775v6#S5.Thmtheorem20) · [Question 5.21](https://arxiv.org/html/2412.20775v6#S5.Thmtheorem21)

## Statement echo

Task #35002 targets `D5/S3/Combinatorics/SpectralGraph/ClosedNeighborhoodCorona/NormalizedLaplacian.normalized_laplacian_charpoly_corona`. The theorem preserves both pairs and the normalized Laplacian convention. [Preregistration](https://github.com/the-omega-institute/trureturing/issues/35002)

| Source clause | Lean statement |
| --- | --- |
| All finite simple undirected graphs | `SimpleGraph V`, `SimpleGraph V'`, `SimpleGraph W` on independent finite vertex types with decidable equality and adjacency |
| The first two graphs are regular | Separate `IsRegularOfDegree` premises for natural degrees `d₁` and `d₂` |
| The first two graphs are adjacency-cospectral | Equality of the real adjacency-matrix characteristic polynomials |
| Closed-neighborhood corona | `corona G H` on `V ⊕ (V × W)`, with every vertex of the copy at `v` joined to the closed neighborhood of `v` in `G` |
| Normalized Laplacian | `normalizedLaplacian` is \(D^{-1/2}(D-A)D^{-1/2}\) with inverse square-root degree defined as zero at degree zero |
| Both factor orders | A conjunction of equal real normalized-Laplacian characteristic polynomials for `corona G₁ H` and `corona G₂ H`, and for `corona H G₁` and `corona H G₂` |

The comparison includes empty vertex types, disconnected graphs and isolated vertices. Equal characteristic polynomials imply equal vertex counts, supplying the equivalence used internally to relabel the regular factors. There are no direct frozen project dependencies.

## Proof

Spectral conjugacy gives an orthogonal intertwiner for the regular adjacency matrices. Their common regular row sum allows a reflection inside the corresponding eigenspace to align the constant vectors. For a regular base, the intertwiner acts on the base and the copy index. For a regular attached factor, it acts within each copy and fixes the cross blocks because it fixes the all-ones vector. In each order the lift has nonzero coefficients only between vertices of equal degree. It therefore intertwines both the degree diagonal and its inverse square-root scaling, giving orthogonal similarity of the normalized Laplacians.

## Declaration shapes

| Public theorem | Proof shape | Live mathematical step |
| --- | --- | --- |
| `Blocks.adjMatrix_corona` | content | The adjacency definition yields both cross blocks and the Kronecker copy block |
| `Blocks.degree_corona_inl` | content | The base row sum includes the size of the closed neighborhood times the copy size |
| `Blocks.degree_corona_inr` | content | The copy row sum adds its internal degree to the size of the corresponding closed neighborhood |
| `RegularIntertwiner.exists_orthogonal_adjacency_intertwiner` | content | Spectral conjugacy and reflection give an orthogonal intertwiner fixing the constant vector |
| `NormalizedLaplacian.normalized_laplacian_charpoly_corona` | content | The two block lifts intertwine adjacency, degree and inverse square-root degree |

The companion names in the table are given relative to their owning modules. The publication theorem has admission basis `open-problem-resolution`. Its two private order-specific proofs use the respective block lifts on the live derivation paths.

## Literature scope

The literature screen in #35002 distinguishes the adjacency, ordinary Laplacian and signless Laplacian conclusions of Theorem 5.20 from the normalized Laplacian question. Literature completeness and priority remain ASSUMED-UNVERIFIED. [Preregistration](https://github.com/the-omega-institute/trureturing/issues/35002)
