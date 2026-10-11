# Commutator gap and scalar translation

## Abstract

The commutator gap controls all scalar translations through a common block frame.

**Definition 1.1 (Commutator operator in Hilbert coordinates).**

$$\forall n \in \mathbb{N}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \operatorname{commOperator}\left(A\right) = \operatorname{toContinuousLinearMap}\left(\operatorname{comp}\left(\operatorname{toLinearMap}\left(\operatorname{vectorize}\left(n\right)\right), \operatorname{comp}\left(\operatorname{LinearMap.mulLeft}(\mathbb{C}, A) - \operatorname{LinearMap.mulRight}(\mathbb{C}, A), \operatorname{toLinearMap}\left(\operatorname{symm}\left(\operatorname{vectorize}\left(n\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/CommutatorGap.commOperator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Conjugate the linear commutator map by vectorize and equip the finite-dimensional map with its continuous structure.

**Definition 1.2 (The commutator norm gap).**

$$\forall n \in \mathbb{N}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \operatorname{gap}\left(A\right) = 2 \cdot \operatorname{RHLinalg.frobSq}(A) - (\Vert \operatorname{commOperator}\left(A\right)\Vert )^{2}$$

*Formalization.* `D5/S3/Quantum/Matrix/CommutatorGap.gap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The gap compares twice the Frobenius square with the squared operator norm of the commutator action.

**Definition 1.3 (Squared matrix operator norm).**

$$\forall n \in \mathbb{N}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \operatorname{opSq}\left(A\right) = (\Vert \operatorname{LinearMap.toContinuousLinearMap}(\operatorname{Matrix.toEuclideanLin}(A))\Vert )^{2}$$

*Formalization.* `D5/S3/Quantum/Matrix/CommutatorGap.opSq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matrix acts on the actual complex Euclidean space.

**Definition 1.4 (Real block comparison matrix).**

$$\forall n \in \mathbb{N}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{Fin}\left(n + 1\right), \mathbb{C}\right), c \in \mathbb{C},\; \operatorname{comparisonMatrix}\left(A, c\right) = [(\Vert A(0, 0)\Vert  + \Vert c\Vert ,\Vert \operatorname{Matrix.submatrix}(A, i\mapsto0, \operatorname{Fin.succ})\Vert _{F});(\Vert \operatorname{WithLp.toLp}(2, \operatorname{Function.comp}(\operatorname{Matrix.col}(A, 0), \operatorname{Fin.succ}))\Vert ,\Vert \operatorname{Matrix.submatrix}(A, \operatorname{Fin.succ}, \operatorname{Fin.succ})\Vert _{F} + \Vert c\Vert )]$$

*Formalization.* `D5/S3/Quantum/Matrix/CommutatorGap.comparisonMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These four nonnegative entries bound the norms of the two output blocks jointly. The subscript F denotes Mathlib's rectangular Frobenius norm.

**Theorem 1.5 (Joint block domination).**

$$\forall n \in \mathbb{N}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{Fin}\left(n + 1\right), \mathbb{C}\right), c \in \mathbb{C},\; \Vert \operatorname{LinearMap.toContinuousLinearMap}(\operatorname{Matrix.toEuclideanLin}(A - c\cdot(1)))\Vert  \le \Vert \operatorname{LinearMap.toContinuousLinearMap}(\operatorname{Matrix.toEuclideanLin}(\operatorname{comparisonMatrix}\left(A, c\right)))\Vert $$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CommutatorGap.blockNorm_domination` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real comparison operator acts on the pair consisting of the head modulus and tail norm of the same input vector.

**Theorem 1.6 (Right unitary invariance).**

$$\forall n \in \mathbb{N}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), U \in \operatorname{Matrix.unitaryGroup}(\operatorname{Fin}\left(n\right), \mathbb{C}),\; \operatorname{RHLinalg.frobSq}(A \cdot \operatorname{val}\left(U\right)) = \operatorname{RHLinalg.frobSq}(A)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CommutatorGap.frobSq_unitary_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Trace cycling cancels the unitary and its conjugateTranspose.

**Theorem 1.7 (Operator square is at most Frobenius square).**

$$\forall n \in \mathbb{N}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \operatorname{opSq}\left(A\right) \le \operatorname{RHLinalg.frobSq}(A)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CommutatorGap.opSq_le_frobSq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Frobenius multiplication inequality bounds every Euclidean input.

**Theorem 1.8 (Nonnegative commutator gap).**

$$\forall n \in \mathbb{N}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; 0 \le \operatorname{gap}\left(A\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CommutatorGap.gap_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A maximizing pure vector provides a unitary block frame and a nonnegative lower bound. The empty dimension is included.

**Theorem 1.9 (Uniform scalar translation bound).**

$$\forall n \in \mathbb{N}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), c \in \mathbb{C},\; \operatorname{opSq}\left(A - c\cdot(1)\right) \le \operatorname{RHLinalg.frobSq}(A) + 2 \cdot \operatorname{Complex.normSq}(c) + 2 \cdot \Vert c\Vert  \cdot \operatorname{Real.sqrt}(\operatorname{gap}\left(A\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CommutatorGap.translation_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A maximizing block frame controls the real comparison matrix by its two-by-two Frobenius norm. Unitary covariance transfers the estimate to A.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/CommutatorGap.blockNorm_domination`
- Truth anchor: `D5/S3/Quantum/Matrix/CommutatorGap.commOperator`
- Truth anchor: `D5/S3/Quantum/Matrix/CommutatorGap.comparisonMatrix`
- Truth anchor: `D5/S3/Quantum/Matrix/CommutatorGap.frobSq_unitary_right`
- Truth anchor: `D5/S3/Quantum/Matrix/CommutatorGap.gap`
- Truth anchor: `D5/S3/Quantum/Matrix/CommutatorGap.gap_nonnegative`
- Truth anchor: `D5/S3/Quantum/Matrix/CommutatorGap.opSq`
- Truth anchor: `D5/S3/Quantum/Matrix/CommutatorGap.opSq_le_frobSq`
- Truth anchor: `D5/S3/Quantum/Matrix/CommutatorGap.translation_gap`
- Dependency: [D5/S3/Quantum/Algebra/GramUnitaryExtension](../Algebra/GramUnitaryExtension.md)
- Dependency: [D5/S3/Quantum/GNSMatrix](../GNSMatrix.md)
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](CartesianVariance.md)
