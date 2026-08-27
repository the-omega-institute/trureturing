# Kernel Towers Recover Nilpotent Block Profiles

## Abstract

Kernel dimensions recover positive nilpotent block profiles and separate the characteristic-polynomial residual.

**Definition 1.1 (Positive block size).**

Lean statement: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.PositiveBlockSize`

*Formalization.* `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.PositiveBlockSize` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A block size is a natural number equipped with a proof that it is positive.

**Definition 1.2 (Block multiset).**

Lean statement: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.BlockMultiset`

*Formalization.* `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.BlockMultiset` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An unordered finite multiset records the positive block sizes.

**Definition 1.3 (Block-profile dimension).**

Lean statement: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.blockProfileDimension`

*Formalization.* `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.blockProfileDimension` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The represented ambient dimension is the sum of all block sizes.

**Definition 1.4 (Nilpotent block profile).**

Lean statement: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.NilpotentBlockProfile`

*Formalization.* `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.NilpotentBlockProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An n-dimensional profile is a block multiset whose sizes sum to n.

**Definition 1.5 (Abstract kernel-dimension tower).**

Lean statement: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.blockKernelTower`

*Formalization.* `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.blockKernelTower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At step k, each block of size s contributes the minimum of k and s.

**Definition 1.6 (Kernel-tower increment).**

Lean statement: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.kernelIncrement`

*Formalization.* `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.kernelIncrement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The named increment is the natural-number difference a_k - a_(k-1).

**Definition 1.7 (Blocks at least a given size).**

Lean statement: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.blockCountAtLeast`

*Formalization.* `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.blockCountAtLeast` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This count selects blocks whose positive size is at least k.

**Definition 1.8 (Blocks of an exact size).**

Lean statement: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.blockCountExactly`

*Formalization.* `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.blockCountExactly` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This count selects blocks whose positive size is exactly k.

**Definition 1.9 (Matrix kernel-dimension tower).**

Lean statement: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.matrixKernelDimensionTower`

*Formalization.* `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.matrixKernelDimensionTower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an actual matrix N, the kth value is the dimension of ker(N^k).

**Definition 1.10 (Unit block size).**

Lean statement: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.unitBlockSize`

*Formalization.* `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.unitBlockSize` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The distinguished positive size one represents a one-by-one block.

**Definition 1.11 (Zero-matrix block profile).**

Lean statement: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.zeroMatrixBlockProfile`

*Formalization.* `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.zeroMatrixBlockProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The n-dimensional zero matrix has n blocks, all of size one.

**Definition 1.12 (Single nilpotent block profile).**

Lean statement: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.singleNilpotentBlockProfile`

*Formalization.* `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.singleNilpotentBlockProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A singleton profile packages one positive nilpotent block.

**Theorem 1.13 (Kernel increments count surviving blocks).**

$$\forall B, k, \operatorname{kernelIncrement}\left(B, k+1\right) = \operatorname{blockCountAtLeast}\left(B, k+1\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.kernel_increment_counts_blocks_at_least` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every positive index k + 1, the tower increment equals the number of blocks whose size is at least k + 1.

**Theorem 1.14 (Successive increments give exact block counts).**

$$\forall B, k, \operatorname{blockCountExactly}\left(B, k\right) = \operatorname{kernelIncrement}\left(B, k\right) - \operatorname{kernelIncrement}\left(B, k+1\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.exact_block_count_from_successive_increments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The number of blocks of size exactly k is b_k minus b_(k+1), including the zero-index boundary.

**Theorem 1.15 (The finite tower recovers the block profile).**

$$\forall n, B, C: \operatorname{NilpotentBlockProfile}\left(n\right),\\{}{\forall k, 1 \leq k \leq n \Rightarrow \operatorname{a}\left(B, k\right) = \operatorname{a}\left(C, k\right)} \Rightarrow B = C.$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.finite_kernel_tower_recovers_block_profile` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two n-dimensional positive block profiles with equal tower values from one through n are equal as multisets.

**Theorem 1.16 (Matrix kernel towers stabilize by dimension).**

$$\forall N: \operatorname{Matrix}\left(n\right), k, n \leq k \Rightarrow \operatorname{matrixKernelDimensionTower}\left(N, k\right) = \operatorname{matrixKernelDimensionTower}\left(N, n\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.matrix_kernel_tower_stabilizes_at_dimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n-dimensional matrix and k at least n, ker(N^k) and ker(N^n) have equal dimensions. Nilpotence is not required.

**Theorem 1.17 (Zero-matrix profile audit).**

$$\operatorname{blockCountExactly}\left(\operatorname{zeroMatrixBlockProfile}\left(n\right), 1\right) = n \land\\{\forall k > 0, \operatorname{a}\left(\operatorname{zeroMatrixBlockProfile}\left(n\right), k\right) = n} \land\\\operatorname{b}\left(\operatorname{zeroMatrixBlockProfile}\left(n\right), 1\right) = n \land {\forall k \geq 2, \operatorname{b}\left(\operatorname{zeroMatrixBlockProfile}\left(n\right), k\right) = 0}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.zero_matrix_block_profile_audit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The n unit blocks give a_k = n for positive k, b_1 = n, and b_k = 0 from step two onward.

**Theorem 1.18 (Single-block profile audit).**

$$\forall s > 0, k,\\{}\operatorname{a}\left(\operatorname{singleNilpotentBlockProfile}\left(s\right), k\right) = \operatorname{min}\left(k, s\right) \land \operatorname{blockCountAtLeast}\left(\operatorname{singleNilpotentBlockProfile}\left(s\right), k\right) = \operatorname{indicator}\left(k \leq s\right) \land\\{}\operatorname{blockCountExactly}\left(\operatorname{singleNilpotentBlockProfile}\left(s\right), k\right) = \operatorname{indicator}\left(s = k\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.single_nilpotent_block_profile_audit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One block of size s has a_k = min(k,s), with the expected indicator counts for at-least and exact sizes.

**Theorem 1.19 (Zero-dimensional profile audit).**

$$\forall B: \operatorname{NilpotentBlockProfile}\left(0\right), B = empty \land {\forall k, \operatorname{a}\left(B, k\right) = 0}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.zero_dimensional_block_profile_audit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A zero-dimensional positive profile is empty and every tower value is zero.

**Theorem 1.20 (One-dimensional profile audit).**

$$\forall B: \operatorname{NilpotentBlockProfile}\left(1\right), B = \operatorname{zeroMatrixBlockProfile}\left(1\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.one_dimensional_block_profile_audit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every one-dimensional positive profile is the singleton unit-block profile of the zero matrix.

**Theorem 1.21 (The positive-index condition is necessary).**

$$\operatorname{kernelIncrement}\left(unitProfile, 0\right) \neq \operatorname{blockCountAtLeast}\left(unitProfile, 0\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.positive_index_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For one unit block, b_0 is zero while one block has size at least zero.

**Theorem 1.22 (Tower equality is necessary for recovery).**

$$\exists B, C: \operatorname{NilpotentBlockProfile}\left(2\right), B \neq C \land \operatorname{a}\left(B, 1\right) \neq \operatorname{a}\left(C, 1\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.kernel_tower_equality_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In dimension two, one size-two block and two size-one blocks are distinct and already have different first tower values.

**Theorem 1.23 (The kernel tower separates the characteristic-polynomial residual).**

$$\operatorname{charpoly}\left(A\right) = \operatorname{charpoly}\left(N\right) \land \operatorname{IsNilpotent}\left(A\right) \land \operatorname{IsNilpotent}\left(N\right) \land \neg\operatorname{Conjugate}\left(A, N\right) \land\\{}\operatorname{a}\left(A, 1\right) = 2 \land \operatorname{a}\left(N, 1\right) = 1 \land \operatorname{a}\left(N, 2\right) = 2.$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.kernel_tower_separates_charpoly_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

FPOD 188.1's zero and square-zero matrices have equal characteristic polynomials and are not conjugate, but their first nullities are two and one.

**Theorem 1.24 (The stabilization bound cannot be removed).**

$$\exists N: \operatorname{Matrix}\left(2\right), \operatorname{matrixKernelDimensionTower}\left(N, 1\right) \neq \operatorname{matrixKernelDimensionTower}\left(N, 2\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.dimension_bound_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A two-dimensional square-zero rational matrix has first nullity one and second nullity two.

## References

- Truth anchor: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.BlockMultiset`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.NilpotentBlockProfile`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.PositiveBlockSize`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.blockCountAtLeast`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.blockCountExactly`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.blockKernelTower`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.blockProfileDimension`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.dimension_bound_is_necessary`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.exact_block_count_from_successive_increments`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.finite_kernel_tower_recovers_block_profile`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.kernelIncrement`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.kernel_increment_counts_blocks_at_least`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.kernel_tower_equality_is_necessary`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.kernel_tower_separates_charpoly_residual`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.matrixKernelDimensionTower`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.matrix_kernel_tower_stabilizes_at_dimension`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.one_dimensional_block_profile_audit`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.positive_index_is_necessary`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.singleNilpotentBlockProfile`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.single_nilpotent_block_profile_audit`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.unitBlockSize`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.zeroMatrixBlockProfile`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.zero_dimensional_block_profile_audit`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.zero_matrix_block_profile_audit`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation](../../Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.md)
