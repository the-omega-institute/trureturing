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

Theorem 5.20 starts with adjacency-cospectral regular graphs \(G_1,G_2\) and a third graph \(H\). It describes two pairs as irregular and nonisomorphic but cospectral (NICS) for adjacency, ordinary Laplacian and signless Laplacian. The pairs are \(G_1\,\underline{\boxtimes}\,H\) versus \(G_2\,\underline{\boxtimes}\,H\) and \(H\,\underline{\boxtimes}\,G_1\) versus \(H\,\underline{\boxtimes}\,G_2\). The underlined box-times denotes the closed-neighborhood corona. [Theorem 5.20](https://arxiv.org/html/2412.20775v6#S5.Thmtheorem20) · [Question 5.21](https://arxiv.org/html/2412.20775v6#S5.Thmtheorem21)

### Statement echo

Task #35002 targets `D5/S3/Combinatorics/SpectralGraph/ClosedNeighborhoodCorona/NormalizedLaplacian.normalized_laplacian_charpoly_corona`. The theorem preserves both pairs and the normalized Laplacian convention. [Preregistration](https://github.com/the-omega-institute/trureturing/issues/35002)

| Source clause | Lean statement |
| --- | --- |
| All finite simple undirected graphs | `SimpleGraph V`, `SimpleGraph V'`, `SimpleGraph W` on independent finite vertex types with decidable equality and adjacency |
| The first two graphs are regular | Separate `IsRegularOfDegree` premises for natural degrees `d₁` and `d₂` |
| The first two graphs are adjacency-cospectral | Equality of the real adjacency-matrix characteristic polynomials |
| Closed-neighborhood corona | `corona G H` on `V ⊕ (V × W)`, with every vertex of the copy at `v` joined to the closed neighborhood of `v` in `G` |
| Normalized Laplacian | `normalizedLaplacian` is \(D^{-1/2}(D-A)D^{-1/2}\) with inverse square-root degree defined as zero at degree zero |
| Both factor orders | A conjunction of equal real normalized-Laplacian characteristic polynomials for `corona G₁ H` and `corona G₂ H`, and for `corona H G₁` and `corona H G₂` |

## Motivation

Question 5.21 asks whether the same closed-neighborhood corona pairs from Theorem 5.20 retain cospectrality after accounting for the degrees of the base and copy vertices.

## Gap

The preceding theorem covers adjacency, ordinary Laplacian and signless Laplacian. The normalized Laplacian additionally scales each row and column by inverse square-root degree. The two factor orders require separate checks of that scaling.

## Route

Spectral conjugacy gives an orthogonal intertwiner for the regular adjacency matrices. Their common regular row sum allows a reflection inside the corresponding eigenspace to align the constant vectors. For a regular base, the intertwiner acts on the base and the copy index. For a regular attached factor, it acts within each copy and fixes the cross blocks because it fixes the all-ones vector. In each order the lift has nonzero coefficients only between vertices of equal degree. It therefore intertwines both the degree diagonal and its inverse square-root scaling, giving orthogonal similarity of the normalized Laplacians.

## Falsifier

A regular adjacency-cospectral pair and an arbitrary finite third graph yielding different normalized-Laplacian characteristic polynomials in either order would refute the claim.

## Evidence

The formal theorem proves the spectral equalities for the survey's pairs and for a wider class that includes isomorphic factors, regular coronas, empty vertex types, disconnected graphs and isolated vertices. Equal characteristic polynomials imply equal vertex counts, supplying the equivalence used internally to relabel the regular factors. There are no direct frozen project dependencies on the publication base.

### Declaration shapes

| Public theorem | Proof shape | Live mathematical step |
| --- | --- | --- |
| `Blocks.adjMatrix_corona` | content | The adjacency definition yields both cross blocks and the Kronecker copy block |
| `Blocks.degree_corona_inl` | content | The base row sum includes the size of the closed neighborhood times the copy size |
| `Blocks.degree_corona_inr` | content | The copy row sum adds its internal degree to the size of the corresponding closed neighborhood |
| `RegularIntertwiner.exists_orthogonal_adjacency_intertwiner` | content | Spectral conjugacy and reflection give an orthogonal intertwiner fixing the constant vector |
| `NormalizedLaplacian.normalized_laplacian_charpoly_corona` | content | The two block lifts intertwine adjacency, degree and inverse square-root degree |

The theorem names are relative to their owning modules. The `admission_basis` is `escape-witness` for the Blocks and RegularIntertwiner modules and `open-problem-resolution` for the Question 5.21 result. The final conjunction consumes both private order-specific proofs.

The following §3.2 helpers organize the proofs through the named live consumers. They provide no independent admission basis or escape witness.

| Module | Private helper | `proof_shape` | Live consumers |
| --- | --- | --- | --- |
| Blocks | `sum_adjMatrix_row` | `bind-only` | `sum_closedNeighborhood_row`, `degree_corona_inl`, `degree_corona_inr` |
| Blocks | `sum_closedNeighborhood_row` | `bind-only` | `degree_corona_inl`, `degree_corona_inr` |
| RegularIntertwiner | `spectralConjugacy` | `bind-only` | `exists_orthogonal_intertwiner_of_row_sum`, `exists_orthogonal_adjacency_intertwiner` |
| RegularIntertwiner | `transpose_unitary` | `bind-only` | `exists_orthogonal_intertwiner_of_row_sum`, `exists_orthogonal_adjacency_intertwiner` |
| RegularIntertwiner | `conjugation_eq` | `bind-only` | `exists_orthogonal_intertwiner_of_row_sum`, `exists_orthogonal_adjacency_intertwiner` |
| NormalizedLaplacian | `charpoly_of_orthogonal_intertwining` | `bind-only` | `normalized_laplacian_charpoly_of_intertwining` |
| NormalizedLaplacian | `blockLift_orthogonal` | `bind-only` | `normalized_laplacian_similarity_of_block` |
| NormalizedLaplacian | `normalized_laplacian_charpoly_of_intertwining` | `bind-only` | `normalized_laplacian_similarity_of_block`, `normalized_laplacian_charpoly_corona_regular_attached` |
| NormalizedLaplacian | `normalized_laplacian_similarity_of_block` | `bind-only` | `normalized_laplacian_charpoly_corona_regular_base` |
| NormalizedLaplacian | `degree_eq_of_regular_intertwiner` | `bind-only` | `normalized_laplacian_charpoly_corona_regular_base`, `normalized_laplacian_charpoly_corona_regular_attached` |
| NormalizedLaplacian | `diagonal_degree_intertwining` | `bind-only` | `normalized_laplacian_charpoly_corona_regular_base`, `normalized_laplacian_charpoly_corona_regular_attached` |
| NormalizedLaplacian | `copyLift_orthogonal` | `bind-only` | `normalized_laplacian_charpoly_corona_regular_attached` |
| NormalizedLaplacian | `normalized_laplacian_charpoly_iso` | `bind-only` | `normalized_laplacian_charpoly_corona` |

### Incomplete §3.9 escape registrations

Five public theorems have outstanding escape registrations under the linked-issue exception. [Audit gaps and selector readings](https://github.com/the-omega-institute/trureturing/issues/35002#issuecomment-7229964615)

| Public theorem | Outstanding evidence |
| --- | --- |
| `Blocks.adjMatrix_corona` | Typed block readout, reconstruction of the scoped `let B` and full block equality, positive law, rejected family, sensitivity, actual dependence and validated binding |
| `Blocks.degree_corona_inl` | Typed degree readout and full law retaining copy cardinality, rejection, sensitivity, actual dependence and validated binding |
| `Blocks.degree_corona_inr` | Typed degree readout and full law retaining both indices and the closed-neighborhood size plus internal copy degree, rejection, sensitivity, actual dependence and validated binding |
| `RegularIntertwiner.exists_orthogonal_adjacency_intertwiner` | Typed realization and full law retaining the existential matrix, both orthogonality equations and adjacency intertwining, with rejection, sensitivity, actual dependence and validated binding |
| `NormalizedLaplacian.normalized_laplacian_charpoly_corona` | Validated binding remains outstanding after the full-law equivalence, positive law, rejected family, sensitivity and actual dependence compiled. The scoped producer reported `declared_unresolved` with `IE-C050` (`incomplete_closure`, `E8.erasure_work`). |

## Triage

The result proves Question 5.21 for both factor orders. The two support conditions relating the lifted intertwiner to equal degrees also account for isolated vertices and empty factors.

### Literature scope

Sonar and Srivastava display the adjacency block identity with the copy coordinates reversed relative to Lean. Theorem 5.20 covers adjacency, ordinary Laplacian and signless Laplacian, and Question 5.21 asks about normalized Laplacian. [Sonar–Srivastava, §3.1](https://arxiv.org/html/2407.05653v2#S3.Ex4) · [Preregistration](https://github.com/the-omega-institute/trureturing/issues/35002)

## ASSUMED-UNVERIFIED

Literature completeness and priority remain unverified.
