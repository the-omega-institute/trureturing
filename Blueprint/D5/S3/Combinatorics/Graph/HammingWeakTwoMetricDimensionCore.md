# Separation and landmark degrees in rectangular Hamming graphs

## Abstract

Weak two-resolving sets in a rectangular Hamming graph are governed by their row degrees, column degrees, and the endpoint degrees of disjoint landmarks.

For natural numbers n and m, the vertices of the Cartesian product of the complete graphs are Fin n times Fin m. The distance, separation sum, and weak resolving property are those of Aryan Kumar, arXiv:2609.32161v1, Section 1. The rectangular weak two-metric dimension below m = 2n - 2 is the question in Section 7.

**Definition 1.1 (Hamming distance).**

$$\forall n \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall x \in \operatorname{Prod}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right)\right),\; \forall y \in \operatorname{Prod}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right)\right),\; \operatorname{dist}\left(x, y\right) = \operatorname{if}\left(\operatorname{fst}\left(x\right) \ne \operatorname{fst}\left(y\right), 1, 0\right) + \operatorname{if}\left(\operatorname{snd}\left(x\right) \ne \operatorname{snd}\left(y\right), 1, 0\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.dist` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For vertices x and y, the distance is the number of coordinates in which they differ: one indicator for the row and one for the column.

**Definition 1.2 (Separation sum).**

Lean statement: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.delta`

*Formalization.* `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.delta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For all natural n and m, a finite set S of vertices, and vertices x and y, delta S x y is the sum over every landmark w in S of the absolute difference between dist x w and dist y w. This absolute difference is Nat.dist, so the sum takes values in the natural numbers.

**Definition 1.3 (Weak resolving property).**

$$\forall n \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall S \in \operatorname{Finset}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right)\right)\right),\; \operatorname{IsWeakResolving}\left(k, S\right) \Leftrightarrow \left(\forall x \in \operatorname{Prod}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right)\right),\; \forall y \in \operatorname{Prod}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right)\right),\; x \ne y \Rightarrow k \le \operatorname{delta}\left(S, x, y\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.IsWeakResolving` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite set S is weak k-resolving exactly when every two distinct vertices have separation at least the natural number k.

**Definition 1.4 (Weak metric dimension).**

Lean statement: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.wdim`

*Formalization.* `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.wdim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For all natural n, m, and k, wdim n m k is the infimum in the natural numbers of the set of cardinalities of finite weak k-resolving sets in Fin n times Fin m. If this set of cardinalities is empty, the infimum is zero. For k equal to two, the entire vertex set is weak resolving, so the infimum is an attained minimum.

**Definition 1.5 (Row degree).**

Lean statement: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.rowDegree`

*Formalization.* `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.rowDegree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite set S of vertices and row i in Fin n, rowDegree S i is the cardinality of the landmarks whose first coordinate equals i.

**Definition 1.6 (Column degree).**

Lean statement: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.colDegree`

*Formalization.* `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.colDegree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite set S of vertices and column j in Fin m, colDegree S j is the cardinality of the landmarks whose second coordinate equals j.

**Theorem 1.7 (Row degree sum).**

Lean statement: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.sum_rowDegree`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.sum_rowDegree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite landmark set S in Fin n times Fin m, the sum of rowDegree S i over all rows i equals the cardinality of S. Every landmark belongs to exactly one row.

**Theorem 1.8 (Column degree sum).**

Lean statement: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.sum_colDegree`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.sum_colDegree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite landmark set S in Fin n times Fin m, the sum of colDegree S j over all columns j equals the cardinality of S. Every landmark belongs to exactly one column.

**Theorem 1.9 (Separation in one row).**

Lean statement: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.delta_same_row`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.delta_same_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite landmark set S, row i, and distinct columns j and j', delta S (i,j) (i,j') equals colDegree S j plus colDegree S j'. A landmark contributes one exactly when its column is one of the two columns, independently of its row.

**Theorem 1.10 (Separation in one column).**

Lean statement: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.delta_same_col`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.delta_same_col` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite landmark set S, distinct rows i and i', and column j, delta S (i,j) (i',j) equals rowDegree S i plus rowDegree S i'. Only landmarks in these two rows contribute.

**Theorem 1.11 (Separation across a rectangle).**

Lean statement: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.delta_rectangle`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.delta_rectangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every S, distinct rows i and i', and distinct columns j and j', delta S (i,j) (i',j') plus twice the membership indicator of (i,j') in S plus twice the membership indicator of (i',j) in S equals the sum of the two row degrees and the two column degrees. The crossed corners have equal distances to the compared vertices and therefore cancel two contributions each.

**Theorem 1.12 (Necessary row pair condition).**

Lean statement: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.row_pair_degree`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.row_pair_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every weak two-resolving set S, distinct rows i and i', and any column j, rowDegree S i plus rowDegree S i' is at least two, by comparing the vertices (i,j) and (i',j).

**Theorem 1.13 (Necessary column pair condition).**

Lean statement: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.col_pair_degree`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.col_pair_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every weak two-resolving set S, any row i, and distinct columns j and j', colDegree S j plus colDegree S j' is at least two, by comparing the vertices (i,j) and (i,j').

**Theorem 1.14 (Degree sum on disjoint landmarks).**

Lean statement: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.disjoint_landmark_degree`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.disjoint_landmark_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every weak two-resolving set S and landmarks (i,j) and (i',j') in distinct rows and distinct columns, rowDegree S i plus colDegree S j plus rowDegree S i' plus colDegree S j' is at least six. Apply the rectangle identity to the crossed corners: the two landmarks subtract four from their degree sum.

**Theorem 1.15 (Sufficient pair degree conditions).**

Lean statement: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.weak_of_pair_degrees`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.weak_of_pair_degrees` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be a finite landmark set. Suppose the degrees of every two distinct rows sum to at least two, the degrees of every two distinct columns sum to at least two, and the four endpoint degrees of every two landmarks in distinct rows and columns sum to at least six. Then S is weak two-resolving. For a rectangle with zero or one crossed landmark, the row and column conditions suffice; with two crossed landmarks, the endpoint condition supplies the remaining separation. Empty rows or columns are allowed whenever the pair conditions hold.

**Theorem 1.16 (Sufficient positive degree conditions).**

Lean statement: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.weak_of_degrees`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.weak_of_degrees` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite landmark set S, suppose every row and every column has degree at least one, and every landmark has the sum of its row and column degrees at least three. Then S is weak two-resolving. Positivity gives both pair conditions, and the two endpoint sums give at least six for disjoint landmarks.

**Theorem 1.17 (The full vertex set resolves).**

Lean statement: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.univ_weak_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.univ_weak_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n and m, the entire set Fin n times Fin m is weak two-resolving. For distinct vertices x and y, the landmarks x and y each contribute dist x y, which is at least one. If there are no distinct vertices, the condition holds vacuously.

**Theorem 1.18 (A resolving set bounds the dimension).**

Lean statement: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.wdim_le_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.wdim_le_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, m, and k and finite weak k-resolving set S in Fin n times Fin m, wdim n m k is at most the cardinality of S, since that cardinality is among the achievable values.

**Theorem 1.19 (Uniform cardinality bounds the dimension).**

Lean statement: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.le_wdim_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.le_wdim_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, m, and a, if every finite weak two-resolving set in Fin n times Fin m has cardinality at least a, then wdim n m 2 is at least a. The full vertex set ensures that the set of achievable cardinalities is nonempty.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.IsWeakResolving`
- Truth anchor: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.colDegree`
- Truth anchor: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.col_pair_degree`
- Truth anchor: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.delta`
- Truth anchor: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.delta_rectangle`
- Truth anchor: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.delta_same_col`
- Truth anchor: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.delta_same_row`
- Truth anchor: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.disjoint_landmark_degree`
- Truth anchor: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.dist`
- Truth anchor: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.le_wdim_two`
- Truth anchor: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.rowDegree`
- Truth anchor: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.row_pair_degree`
- Truth anchor: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.sum_colDegree`
- Truth anchor: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.sum_rowDegree`
- Truth anchor: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.univ_weak_two`
- Truth anchor: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.wdim`
- Truth anchor: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.wdim_le_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.weak_of_degrees`
- Truth anchor: `D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.weak_of_pair_degrees`
