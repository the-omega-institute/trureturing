# Balanced commutators in SU(2)

## Abstract

A determinant-one two-dimensional unitary is exactly a commutator of determinant-one unitaries at square-root distance from identity.

Mat denotes complex 2 by 2 matrices with the Euclidean L2 operator norm. SU(U) means unitarity and determinant one. star is the matrix adjoint, so VW star(V) star(W) is the group commutator. All statements and proofs in this support module are Apache-2.0 reuse of Zayn Blore's CSD SU2Rotation and CommutatorDecomposition at commit 9b2d2c17e926ae13795119c5f2f62e85ea240c2d. Original file and declaration references are in the Lean source; the full license is docs/reports/qmutualinfo/csd-lean4-LICENSE.txt.

**Theorem 1.1 (Distance of a unit quaternion matrix).**

$$\forall w \in \operatorname{Real}\left(\right),\; \forall x \in \operatorname{Real}\left(\right),\; \forall y \in \operatorname{Real}\left(\right),\; \forall z \in \operatorname{Real}\left(\right),\; w^{2} + x^{2} + y^{2} + z^{2} = 1 \Rightarrow \left\lVert \operatorname{suTwo}\left(w, x, y, z\right) - 1 \right\rVert = \operatorname{sqrt}\left(2 - 2 \cdot w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/BalancedSU2Commutator.norm_su2_sub_one` (`✓ std3`). ∎

*Citation.* Christopher M. Dawson; Michael A. Nielsen (2006). *The Solovay-Kitaev algorithm*. URL: <https://arxiv.org/abs/quant-ph/0505030>.

*Commentary.*

The scalar part of a unit quaternion determines its operator-norm distance to identity. The C-star identity reduces this to star(M)M being a scalar multiple of the identity.

**Theorem 1.2 (Exact balanced decomposition).**

$$\forall U \in \operatorname{Mat}\left(\right),\; \left(U \in \operatorname{unitary}\left(\operatorname{Mat}\left(\right)\right) \land \operatorname{det}\left(U\right) = 1\right) \Rightarrow \left(\exists V \in \operatorname{Mat}\left(\right),\; \exists W \in \operatorname{Mat}\left(\right),\; \left(V \in \operatorname{unitary}\left(\operatorname{Mat}\left(\right)\right) \land \operatorname{det}\left(V\right) = 1\right) \land \left(\left(W \in \operatorname{unitary}\left(\operatorname{Mat}\left(\right)\right) \land \operatorname{det}\left(W\right) = 1\right) \land \left(U = V \cdot W \cdot \operatorname{star}\left(V\right) \cdot \operatorname{star}\left(W\right) \land \left(\left\lVert V - 1 \right\rVert \le \operatorname{sqrt}\left(2\right) \cdot \operatorname{sqrt}\left(\left\lVert U - 1 \right\rVert\right) \land \left\lVert W - 1 \right\rVert \le \operatorname{sqrt}\left(2\right) \cdot \operatorname{sqrt}\left(\left\lVert U - 1 \right\rVert\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/BalancedSU2Commutator.exists_commutator_of_det_one` (`✓ std3`). ∎

*Citation.* Christopher M. Dawson; Michael A. Nielsen (2006). *The Solovay-Kitaev algorithm*. URL: <https://arxiv.org/abs/quant-ph/0505030>.

*Commentary.*

Write the target as a unit quaternion. Two rotations about orthogonal axes produce a standard commutator at exactly the target distance from identity; its scalar part therefore agrees with the target. Reflection through the bisector aligns their vector parts. In the antipodal case, swap the two factors to take the adjoint. Unitary conjugation preserves both factor distances and determinant one. The decomposition is exact, with both factors bounded by sqrt(2)*sqrt(norm(U-1)).

## References

- Truth anchor: `D5/S3/Quantum/Approximate/BalancedSU2Commutator.exists_commutator_of_det_one`
- Truth anchor: `D5/S3/Quantum/Approximate/BalancedSU2Commutator.norm_su2_sub_one`
