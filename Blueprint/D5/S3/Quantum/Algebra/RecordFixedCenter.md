# The Center of a Record-Block Algebra

## Abstract

The center of a record-block algebra is exactly its block-scalar range.

**Theorem 1.1 (The record-block center is the block-scalar range).**

$$\forall \Lambda, I,\ [\forall \alpha, \operatorname{Fintype}(I_{\alpha})],\ [\forall \alpha, \operatorname{DecidableEq}(I_{\alpha})],\ Z(\prod_{\alpha\in \Lambda} M_{I_{\alpha}}(\mathbb{C})) = \operatorname{range}(\operatorname{recordCenterScalar}_{I}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/RecordFixedCenter.record_fixed_center_eq_block_scalars` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Lambda index the record-indistinguishability classes and let I alpha be the finite set of addresses in class alpha. Under the preceding fixed-algebra decomposition, the fixed algebra is the product of the full matrix algebras on these blocks. The source address set, hence its label set, is finite, so this product is the source statement's finite direct sum.

Mathlib identifies the center of a product pointwise and identifies the center of every full complex matrix algebra with its scalar matrices. Choosing the scalar in each block gives exactly the range of recordCenterScalar, and every such block-scalar family is central.

The coordinate alpha is therefore the independently variable classical record label. The matrix block on I alpha remains unrestricted in the fixed algebra, while its center retains only a scalar multiple of the identity; this is the unresolved internal quantum freedom described by the source corollary.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/RecordFixedCenter.record_fixed_center_eq_block_scalars`
