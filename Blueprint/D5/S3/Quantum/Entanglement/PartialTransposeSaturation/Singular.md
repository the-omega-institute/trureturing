# Singular chains

## Abstract

Exact tensor ranks of extracted singular chains

The construction treats a pair of complex linear maps on finite dimensional spaces. Kernel chains are split by commuting source and target projections. Their actual span bases identify the restricted arrows with rectangular singular pencil blocks. Common zero rows and columns are retained through zero index blocks. Classical matrix pencil decompositions provide the context; the chain splitting and tensor rank arguments here are proved directly.

**Definition 1.1 (Truncated identity coefficient).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.rightE`

*Formalization.* `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.rightE` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

The r by r+1 complex matrix with an identity in the first r columns and a final zero column.

**Definition 1.2 (Shift coefficient).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.rightF`

*Formalization.* `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.rightF` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

The r by r+1 complex matrix with an initial zero column followed by an identity.

**Definition 1.3 (Extracted source span).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.source`

*Formalization.* `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.source` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

The complex span of the independent coefficient vectors in an extracted polynomial kernel chain.

**Definition 1.4 (Extracted target span).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.target`

*Formalization.* `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.target` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

The span of the second arrow applied to all chain vectors except the final one.

**Definition 1.5 (Source chain basis).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.sourceBasis`

*Formalization.* `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.sourceBasis` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

The independent chain vectors form a basis of their own span, including the singleton basis for a zero index.

**Definition 1.6 (Target chain basis).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.targetBasis`

*Formalization.* `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.targetBasis` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

The independent output chain vectors form a basis of their own span, including the empty basis for a zero index.

**Definition 1.7 (Restricted first arrow).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.firstBlock`

*Formalization.* `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.firstBlock` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

Restrict the first arrow to the source chain span and project to the target chain span. Commutation of the two span projections makes this equal to the original first arrow on that source.

**Definition 1.8 (Restricted second arrow).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.secondBlock`

*Formalization.* `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.secondBlock` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

Restrict the second arrow to the source chain span and project to the target chain span. The resulting map equals the original second arrow on the source chain span.

**Definition 1.9 (Extracted finite pencil).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.block`

*Formalization.* `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.block` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

The two restricted arrows, with their actual finite dimensional source and target spans, form a finite pencil.

**Definition 1.10 (Complementary source projection).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.sourceComplementProjection`

*Formalization.* `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.sourceComplementProjection` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

Subtract the source span projection from the identity and restrict its output to the kernel of the source span projection.

**Definition 1.11 (Complementary target projection).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.targetComplementProjection`

*Formalization.* `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.targetComplementProjection` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

Subtract the target span projection from the identity and restrict its output to the kernel of the target span projection.

**Theorem 1.12 (Tensor rank over the chain splitting).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.tensor_split`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.tensor_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

For every second finite pencil, the tensor sum rank of the original pencil is the sum of the ranks for its extracted chain and its actual complementary pencil. The projected component factors through a surjection onto the source span and an injection from the target span; the complementary component has the corresponding factorization through the two projection kernels.

**Theorem 1.13 (Horizontal rank over the chain splitting).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.horizontal_split`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.horizontal_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

The horizontal pair map has the sum of the horizontal ranks of the extracted chain and its simultaneous complement. Apply image rank additivity to the common target projection and the product of the two source projections.

**Theorem 1.14 (Vertical rank over the chain splitting).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.vertical_split`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.vertical_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

The joint pair map has the sum of the vertical ranks of the extracted chain and its simultaneous complement. The target projection acts independently on the two output components.

**Theorem 1.15 (Horizontal rank of an extracted chain).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.horizontal_rank`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.horizontal_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

A chain of index r has horizontal pair rank r. The second restricted arrow is onto the entire target chain span.

**Theorem 1.16 (Vertical rank of an extracted chain).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.vertical_rank`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.vertical_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

A positive index r chain has vertical pair rank r+1. Its two arrows have trivial common kernel: the first arrow recovers all source coordinates after the initial coordinate, and the second arrow recovers the initial coordinate. A zero index chain is a common zero column and has vertical rank zero.

**Theorem 1.17 (Tensor rank of two right chains).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.tensor_rank`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.tensor_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

For actual extracted chains of indices r and s, the two term tensor sum has rank r times s, including zero indices. Their chain bases identify the two restricted arrows with the shift and truncated identity matrices. Transpose injectivity of the same orientation matrix follows by induction on the first row index, starting from the unshifted boundary.

**Theorem 1.18 (Tensor rank after one chain is dualized).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.partialTranspose_rank`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.partialTranspose_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

Dualizing the first of two extracted right chains gives tensor rank r times s plus min(r,s). The exact mixed rectangular pencil rank is reused after passing to the actual chain span bases and their dual bases.

**Theorem 1.19 (Tensor rank of opposite chain orientations).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.mixed_tensor_rank`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.mixed_tensor_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

Dualizing the second of two extracted right chains also gives tensor rank r times s plus min(r,s). This is the opposite orientation singular block formula, valid at zero indices as well.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.block`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.firstBlock`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.horizontal_rank`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.horizontal_split`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.mixed_tensor_rank`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.partialTranspose_rank`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.rightE`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.rightF`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.secondBlock`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.source`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.sourceBasis`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.sourceComplementProjection`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.target`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.targetBasis`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.targetComplementProjection`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.tensor_rank`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.tensor_split`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.vertical_rank`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular.vertical_split`
- Dependency: [D5/S3/Quantum/Entanglement/PartialTransposeSaturation/ChainSplitting](ChainSplitting.md)
- Dependency: [D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition](Decomposition.md)
- Dependency: [D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency](Sufficiency.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks](../../TensorNetworks/BridgeGraph/ShiftPencilBlocks.md)
