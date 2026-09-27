---
bibkey: kade2025boxsixvertex
authors: Moritz Kade
year: 2025
title: "Integrable systems: From the ice rule to supersymmetric fishnet Feynman diagrams"
doi: 10.18452/33769
url: https://arxiv.org/abs/2509.03416v1
claim: "Section 2.3 of the thesis introduces box boundary conditions for the six-vertex model, with arrow-reflecting diagonal K-matrices on all four walls, and conjectures a determinant formula for the partition function of the square box with 2M horizontal and 2M vertical spectral lines."
strata_touched:
  - D5/S3/StatisticalMechanics/VertexModels/KadeBoxBoundaryRefutation
license: citation-only
triage: anchor
---

# Kade, box boundary conditions for the six-vertex model

Section 2.3, "The box boundary condition", of the thesis considers a square
lattice bounded by walls on all four sides, with pairs of spectral lines
`x_i, 1/x_i` running from the right wall to the left wall and pairs
`y_j, 1/y_j` running from the top wall to the bottom wall. The bulk weights are

> [a : b : c] = [p x − p^{−1} x^{−1} : x − x^{−1} : p − p^{−1}]

and the arrow-reflecting walls carry the diagonal K-matrices
`K_L(x) = diag(b(xξ_L), b(x/(qξ_L)))`, `K_R(x) = diag(b(xξ_R), b(xq/ξ_R))`,
`K_U(y) = diag(b(yξ_U), b(yq/ξ_U))`, `K_D(y) = diag(b(yξ_D), b(y/(qξ_D)))`.
The thesis derives a recursion at `x_m = y_n` and then proposes, for the square
case `M = N`, the solution

> Z_M({x_i}|{y_i}) = ∏_{i,j} (x_i/y_j − y_j/x_i) W(x_i, y_j) / ∏_{i<j} (x_j/x_i − x_i/x_j)(y_i/y_j − y_j/y_i)
> · det[ c² a(x_i y_j) a(1/(x_i y_j)) F^LU(x_i) F^DR(y_j) / ((x_j/y_i − y_i/x_j) W(x_i, y_j)) ]

with `W(x, y) = a(xy) a(1/(xy)) a(x/y) a(y/x)`,
`F^LU(x) = b(xξ_L) b(xq/ξ_U) + b(x/(qξ_L)) b(xξ_U)` and
`F^DR(y) = b(yξ_D) b(yq/ξ_R) + b(y/(qξ_D)) b(yξ_R)`. The concluding chapter
states that this conjecture "has to be proven or discarded".

## Verified locator

- DOI: 10.18452/33769 (listed by the arXiv API for the record; resolves through doi.org to the Humboldt-Universität edoc handle 18452/34401, checked 2026-09-27).
- URL: https://arxiv.org/abs/2509.03416v1 (the only version listed by the arXiv
  API on 2026-09-27); source file `parts/part2/square_ice_and_the_6v_model.tex`,
  section "The box boundary condition", equations
  `eq:6V_BoxPartitionFunctionSquareSolution`, `eq:6V_WFactor`,
  `eq:6V_ArrowReflectingKMatrices` and the trace functions after it; figures
  `figures/vertexmodel/partition_function/box_partitionfunction_MN.pdf`,
  `figures/vertexmodel/Kmatrix/*/K*_mat.pdf`, `figures/vertexmodel/6vertices/6Vvertices.pdf`
  and `figures/vertexmodel/Rmatrix/Rmatrix_mat_8V.pdf`.
