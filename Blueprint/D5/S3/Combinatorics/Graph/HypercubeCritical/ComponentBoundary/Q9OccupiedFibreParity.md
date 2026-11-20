# Occupied fibre counts by projected parity

## Abstract

Occupied fibre counts by projected parity

**Theorem 1.1 (An exact parity identity for Huang-balanced cubic supports).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9OccupiedFibreParity.occupied_fibre_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9OccupiedFibreParity.occupied_fibre_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Delete any one axis from a Huang-balanced induced cubic support in Q9. For a projected parity b, let P_b count the occupied fibres and m_b count the fibres with both endpoints selected. The total count m of selected edges along the deleted axis is m_b + m_(1−b).

The signed coordinate action along the deleted axis flips that bit and multiplies by the Huang edge sign. It squares to the identity and anticommutes with the other coordinate actions. The zero-extended switching vector is a 3-eigenvector of the sum of the signed actions. Taking the inner product of the anticommutator with that vector gives 3 times its inner product with the axial action equal to its squared norm. Each selected axial edge contributes two to the first inner product by switching balance, and each support vertex contributes one to the squared norm. Thus the support has 6m vertices.

In projected parity b, the support contains P_b + m_b vertices. Each selected transverse edge has exactly one endpoint in each projected parity, so its contributions cancel when the two degree sums are subtracted. The axial contribution in parity b is 2m_b. Adding the total degree sum to the degree-sum difference gives 3 P_b = 7m + m_(1−b).

For Hong, Wu and Xia's Problem 2, suppose shell counts supply 26 empty fibres in one projected parity and 16 double fibres in the opposite parity. These counts arise from two parallel eightfold exterior covers whose projected centers have equal parity and Hamming distance at least six. The empty fibres leave at most 102 occupied fibres out of 128. The identity gives 7m + 16 ≤ 306, so m ≤ 41 and the support has at most 246 vertices. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9OccupiedFibreParity.occupied_fibre_identity`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedIncidence](Q9FoldedIncidence.md)
