# Record Fixed Algebra Decomposition

## Abstract

A finite record fixed algebra decomposes into its matrix blocks.

**Theorem 1.1 (The record fixed algebra is the product of its matrix blocks).**

$$\forall \Lambda, I,\ [\forall alpha, \operatorname{Fintype}(I_{alpha})],\ [\forall alpha, \operatorname{DecidableEq}(I_{alpha})],\ \operatorname{AlgEquiv}(recordFixedAlgebra(I), (alpha \mapsto \operatorname{M}_{I_{alpha}}(\mathbb{C})))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FixedAlgebra/RecordFixedAlgebraDecomposition.record_fixed_algebra_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite index type Lambda and finite address types I alpha, the block-diagonal embedding places one arbitrary complex matrix in each record class and realizes the fixed algebra as its range.

The block-diagonal map is injective because extracting each diagonal block is a left inverse. Its range restriction is therefore a bijective algebra homomorphism, and Mathlib's AlgEquiv.ofBijective packages the resulting algebra isomorphism.

Repository search found the finite-entry fixed-point characterization and the block-center result, but no general fixed-algebra decomposition. The source also explicitly records that this general finite-dimensional decomposition remains an open proof gap; the present statement supplies the block-diagonal algebra realization needed for the displayed decomposition.

## References

- Truth anchor: `D5/S3/Quantum/FixedAlgebra/RecordFixedAlgebraDecomposition.record_fixed_algebra_decomposition`
