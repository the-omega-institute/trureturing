# Switching parity of folded signed rows

## Abstract

A signed modulo-four constraint can reject a local folded profile whose every pair of rows is feasible.

**Theorem 1.1 (Exact signed rows prescribe the parity of an even cut).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedSignedRows.signed_rows_even_cut`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedSignedRows.signed_rows_even_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a finite vertex set with symmetric neighbour sets N(u) and signs encoded by bits. A switch z adds the sum z(u) + z(v) to the bit on each edge uv over the field of two elements. Define the Laplacian by summing z(u) + z(v) over N(u). Let X be a set of vertices whose indicator is killed by this Laplacian. Equivalently each vertex has an even number of incident edges crossing X.

Suppose the switched integer sum on each row u in X equals t(u). Subtract that sum from the degree and divide by two in the integers to count the negative terms. Reducing these counts modulo two retains the signed row equations modulo four. Their sum over X equals the sum of the original sign bits in those rows. Symmetry of the neighbour relation makes the Laplacian self-adjoint, so the switching contribution pairs to zero with the indicator of X. For symmetric signs the original sum counts internal edges twice and gives the parity of the negative edges crossing X.

Fold along the last coordinate of Q₉ in the Huang sign convention where the sign of an edge in direction i is the parity of the preceding coordinates, encoded as ±1. The axial sign at a projected vertex u is p(u) = (−1) raised to the Hamming weight of u. Assume a signed cubic support whose labels are ±1 on selected vertices and zero off the support, with every selected edge satisfied and a zero Huang row sum at each unselected endpoint. At a singleton u with selected label σ(u), the missing-endpoint row gets the axial term p(u)σ(u), and opposite-layer singleton neighbours contribute h(u,v)σ(v).

A neighbouring dimer supplies an endpoint in the selected layer of u and an endpoint in the missing layer. Satisfaction of its transverse edge fixes the first label relative to σ(u), and satisfaction of its axial edge multiplies that label by p(v) to obtain the other label. Since p(v) = −p(u) and the transverse Huang sign is independent of the last coordinate, each dimer contributes −p(u)σ(u) to the missing row. If k(u) counts those dimers and the listed opposite-layer singleton neighbours exhaust the other terms, multiplying the zero row by σ(u) gives the symmetric target p(u)(k(u) − 1).

**Theorem 1.2 (Every pair is feasible in a six-site profile with an inconsistent cut).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedSignedRows.six_row_separation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedSignedRows.six_row_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In order a, b, c, d, x, y the first four transverse bits are 0000, 1000, 1100, 0100, 0010 and 1001, with four trailing zeros. Take singleton layers according to transverse parity. The edges are ab, bc, cd, da, ax and by. The original negative edges are bc and by. The target vector (−1, −1, 2, 0, 1, 1) corresponds to the dimer counts (0, 2, 3, 1, 0, 2) under the stated row premises.

Each of the fifteen unordered pairs admits a switching satisfying both exact integer rows. For X = {a, c, x}, the crossing edges form the square abcd. This cut has even degree at every vertex, and its only negative edge is bc. The required numbers of negative incidences in the three rows are 2, 0 and 0. Their total is even, so the three rows are inconsistent and the six rows have no common solution.

This local test applies when the rows use all relevant incidences or when their targets already account for omitted incidences. For the displayed dimer counts, ordinary component balance also excludes the profile as a closed component because the counts sum to eight. The six-site example separates the even-cut condition from independent signed row-pair feasibility. The full value of f₂(Q₉) in Hong, Wu and Xia's Problem 2 remains open. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedSignedRows.signed_rows_even_cut`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedSignedRows.six_row_separation`
