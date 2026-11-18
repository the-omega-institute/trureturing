# Sufficiency

## Abstract

Concatenation criteria sufficient for partial transpose saturation

All ranks are ordinary complex matrix ranks. Index types may be arbitrary finite types, including empty types. Wang and Chen give the general bound that partial transpose rank is at most the number of tensor summands times the original rank. The assertions here prove two sufficient equality families for two summands.

**Definition 1.1 (Two coefficient tensor sum).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.tensorSum`

*Formalization.* `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.tensorSum` (`✓ std3`).

*Citation.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

For arbitrary complex rectangular coefficient matrices the row index is the ordered product of output indices and the column index is the ordered product of input indices. The matrix is A1 tensor B1 plus A2 tensor B2.

**Definition 1.2 (First factor partial transpose).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.partialTranspose`

*Formalization.* `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.partialTranspose` (`✓ std3`).

*Citation.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

Transpose both first-factor coefficient matrices while retaining the second-factor pair. The first-factor input and output indices exchange places. This convention agrees with first-factor transposition in the source rank inequality.

**Definition 1.3 (Horizontal concatenation rank).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.hRank`

*Formalization.* `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.hRank` (`✓ std3`).

*Citation.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

The ordinary matrix rank of the horizontal concatenation of the two coefficient matrices.

**Definition 1.4 (Vertical concatenation rank).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.vRank`

*Formalization.* `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.vRank` (`✓ std3`).

*Citation.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

The ordinary matrix rank of the vertical concatenation of the two coefficient matrices.

**Theorem 1.5 (An independent pair detects both other coefficients).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.tensorSum_eq_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.tensorSum_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

If A1 and A2 are linearly independent as matrices, their tensor sum with B1 and B2 vanishes exactly when both B1 and B2 vanish. Coefficient independence applies separately at every second-factor matrix entry. Empty and rectangular index types are included.

**Theorem 1.6 (Coordinate invariance of tensor sum rank).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.rank_tensorSum_change`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.rank_tensorSum_change` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

When all four square change matrices have invertible determinants, the transformed tensor sum has the original rank.

**Theorem 1.7 (Independent prescription of the two outputs).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.joint_control_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.joint_control_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

Vertical concatenation rank is twice horizontal concatenation rank exactly when every ordered pair of vectors in the sum of the coefficient images is attained by the joint output map. Its image lies in the product of that common image with itself. Equal finite dimensions force equality of the two subspaces.

**Theorem 1.8 (Tensor rank from independent output control).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.rank_tensorSum_of_jointSurjective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.rank_tensorSum_of_jointSurjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

Suppose the second pair can attain every ordered pair of vectors in its combined image. The tensor sum has rank equal to the product of the dimensions of the combined images of the two pairs. For each pure tensor, prescribe one second-factor output and set the other to zero. These preimages give both inclusions in the exact tensor rectangle range equality. The dimension of that rectangle is the product of the dimensions of its factors.

**Theorem 1.9 (The untransposed rank from one saturated pair).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.rank_tensorSum_of_vertical_saturated`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.rank_tensorSum_of_vertical_saturated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

For arbitrary A1 and A2, if the vertical rank of the B pair is twice its horizontal rank, the tensor sum has rank hA times hB. No independent coefficient assumption is needed.

**Theorem 1.10 (The transposed rank from one saturated pair).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.rank_partialTranspose_of_vertical_saturated`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.rank_partialTranspose_of_vertical_saturated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

Under the same hypothesis on B, the first-factor partial transpose has rank vA times hB. Apply the tensor rank formula to the transposed A pair and use the concatenation transpose identity.

**Theorem 1.11 (The vertical saturation family).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.saturation_of_vertical`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.saturation_of_vertical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

If vA equals twice hA and vB equals twice hB, the tensor sum has rank hA times hB and its partial transpose has twice that rank.

**Theorem 1.12 (The horizontal saturation family).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.saturation_of_horizontal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.saturation_of_horizontal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

If hA equals twice vA and hB equals twice vB, the partial transpose again has twice the original rank. Transpose both coefficient pairs, apply the vertical family, and use invariance of rank under full transposition.

**Theorem 1.13 (Tensor rank in arbitrary finite bases).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.finrank_tensorSum_toMatrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.finrank_tensorSum_toMatrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

The rank of the sum of two tensor products of linear maps equals the rank of the Kronecker sum of their matrices in any four finite bases. Tensor product bases identify the maps, and matrix rank is the dimension of their image.

**Theorem 1.14 (Sufficiency of the concatenation test).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.sufficient`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.sufficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

For any four finite rectangular complex coefficient matrices, either pair of matching concatenation rank equalities implies that the partial transpose has twice the original rank. This is the sufficient direction of the proposed criterion. It imposes no linear independence assumptions. The necessity direction for arbitrary coefficient pairs is outside this statement.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.finrank_tensorSum_toMatrix`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.hRank`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.joint_control_iff`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.partialTranspose`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.rank_partialTranspose_of_vertical_saturated`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.rank_tensorSum_change`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.rank_tensorSum_of_jointSurjective`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.rank_tensorSum_of_vertical_saturated`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.saturation_of_horizontal`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.saturation_of_vertical`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.sufficient`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.tensorSum`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.tensorSum_eq_zero_iff`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.vRank`
- Dependency: [D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnTensor](../../../Combinatorics/SubspaceCodes/MRDDensityColumnTensor.md)
