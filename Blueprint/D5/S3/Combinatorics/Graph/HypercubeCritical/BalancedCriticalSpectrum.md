# Spectral constraints on balanced critical cube subgraphs

## Abstract

The switching vector of a balanced regular induced subgraph of a square-dimensional cube satisfies the ambient Huang equation, and every direction has equally many edges.

The external research anchor is Hong, Wu and Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, 7 October 2026, Section 7, Problem 2: Determine whether f₂(Q₉)=3 or 4. The exact source is https://arxiv.org/html/2610.09483v1#Thmproblem2 . That problem asks for 258 vertices inducing maximum degree at most three, or a complete exclusion. This module proves a structural constraint under the additional hypotheses of exact regularity and switching balance. It does not resolve that problem.

The matrix is exactly the existing private huangMatrix from HypercubeSubQuorum, defined using the basis and operator in the pinned Archive.Sensitivity. Its symmetry and energy identity are reused. No second proof of the square identity or spectral theory is supplied. TRUE selects the first recursive block in Archive.Sensitivity; therefore its directional signs count earlier FALSE coordinates. The balance assumption below uses these matrix entries directly. GridWedgeComponent uses earlier TRUE coordinates instead. This module does not claim a compiled gauge or complement bridge between them.

General equality regularity and switching mechanisms are prior work of Laplante, Naserasr, Sunny and Wang, Sensitivity conjecture and signed hypercubes, https://hal.science/hal-04080411/document , commentary after Lemma 4.1 and Theorem 6.2. Clifford and exterior-algebra formulations appear in Karasev, https://arxiv.org/abs/1907.11175v2 , Sections 1.2–1.3, and Mathews, https://arxiv.org/abs/1907.12357v2 , Sections 2.2–2.3. The module is a repository derivation of the explicit ambient and directional consequences, with no claim of literature priority. A lower bound of 48 and the classification of possible supports remain outside this formal result.

**Definition 1.1 (Balance of the actual induced cube edges).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum.IsBalanced`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum.IsBalanced` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vertex set is a finite subset of the actual Boolean functions on Fin n. Balance means that a real switching function takes values plus or minus one on the selected vertices, and every selected hypercube edge has matrix coefficient equal to the product of its endpoint values. No eigen-equation or vanishing condition outside the selected set is included in this assumption.

**Theorem 1.2 (The operator is an actual coordinate flip).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum.gamma_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum.gamma_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The recursive direction operator on Sensitivity.V is transported once through its existing basis. Its value at x is exactly the Huang entry at x and flip_i(x), multiplied by the input at flip_i(x). Thus the direction index is a real cube coordinate.

**Theorem 1.3 (The ambient and directional operators).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum.anticommutator`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum.anticommutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every dimension and every actual direction, A gamma_i plus gamma_i A is twice the identity. The proof follows the existing recursive Huang operator and the explicit direction recursion.

**Theorem 1.4 (Internal balance forces the full ambient equation).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum.ambient_eigenvector`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum.ambient_eigenvector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In dimension d squared, assume the actual induced graph is regular of degree d and fix a switching function. Extend it by zero. Actual induced neighbor counts prove A z equals d z on the support. These entries already exhaust Huang's full squared norm identity, so every outside entry of A z is zero. The result is a full ambient equation. An empty support gives the zero vector; nonemptiness is needed to call it a nonzero eigenvector, and connectedness is never assumed.

**Theorem 1.5 (Every direction has the same edge count).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum.direction_edge_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum.direction_edge_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual coordinate i, twice d times the number of selected i-edges is the support cardinality. Each edge is counted exactly once at its FALSE endpoint. Symmetry and the anticommutator turn the ambient equation into d times the number of selected endpoints in direction i equals the support size. The actual flip involution pairs the FALSE and TRUE endpoint sets. The dimension-zero case has no direction indices; it does not assert the existence of an edge.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum.IsBalanced`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum.ambient_eigenvector`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum.anticommutator`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum.direction_edge_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum.gamma_apply`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeSubQuorum](../HypercubeSubQuorum.md)
