---
bibkey: molinari2022graphene
authors: L. G. Molinari
year: 2022
title: "Graphene nanocones and Pascal matrices"
doi: 10.48550/arXiv.2206.14428
url: https://arxiv.org/abs/2206.14428v2
claim: "Conjecture 2: the Hückel determinant of a honeycomb trapezium equals the displayed reduced Pascal determinant."
strata_touched:
  - D5/S3/Combinatorics/Graph/HoneycombTrapeziumHuckelDeterminant
license: citation-only
triage: anchor
---

# Graphene nanocones and Pascal matrices

L. G. Molinari, arXiv:2206.14428v2 (2022-08-21), math-ph.

Page 4 defines the horizontal blocks:

> A block Tₘ(xₘ,yₘ) is a square matrix of size 2m+1 that describes a row of 2m+1 atoms with boundary parameters xₘ,yₘ:

The displayed $T_0$ is $x_0+y_0$. For $m>0$ the block has ones on the two adjacent diagonals, $y_m$ at $(0,2m)$ and $x_m$ at $(2m,0)$. The vertical blocks are defined on the same page:

> The blocks Rₘ are (2m+1)×(2m−1), with unit elements for the vertical edges in the graph, joining atoms in rows m−1 and m:

The displayed $R_1,R_2,R_3$ have ones at $(2j+1,2j)$, $0\leq j<m$. The triangle matrix has $T_m$ on the diagonal and $R_m,R_m^T$ on its adjacent block diagonals.

Section 5, page 9, defines the trapezium:

> If rows 0,1,...,k−1 are removed from a honeycomb triangle, a trapezium results, with rows of lengths 2k+1, ... , 2n+1. The corresponding Hückel matrix Hₖ,ₙ(𝐱,𝐲) is obtained by deleting the first k² rows and columns of Hₙ(𝐱,𝐲). Its size is (n+1)²−k²=(2k+1) + ... + (2n+1).

Conjecture 2, verbatim (page 9):

> The determinant of the Hückel matrix Hₖ,ₙ(𝐱, 𝐲) of a honeycomb trapezium with rows with 2k+1, 2k+3, ... , 2n+1 sites, size (n+1)²−k², is equal to the determinant of the following matrix of size n+1−k:

The displayed matrix has indices $0\leq i,j\leq n-k$, with rows in decreasing source-row order:

$$
M_{ij}=\begin{cases}
x_{n-i}+y_{n-i},&i=j,\\
(-1)^{j-i}\binom{n-i}{j-i}y_{n-i},&i<j,\\
\binom{n-j}{i-j}x_{n-j},&i>j.
\end{cases}
$$

The identity is read over any commutative ring with arbitrary boundary weights. Its $k=0$ specialization is the paper's Conjecture 1 for triangles; Conjecture 2 is the assertion treated here. No assertion about Conjecture 3 on permanents is made.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2206.14428
- URL: https://arxiv.org/abs/2206.14428v2
- PDF: https://arxiv.org/pdf/2206.14428v2, page 4 for the blocks and page 9 for Conjecture 2.
- Original source: https://arxiv.org/src/2206.14428v2, `HUCKEL_PASCAL_3.tex`, Conjecture 2 and its following determinant display.
