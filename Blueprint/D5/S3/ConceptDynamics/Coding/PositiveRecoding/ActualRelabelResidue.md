# Actual relabel row matrices equal the reduced forward gyration

## Abstract

Actual relabel row matrices equal the reduced forward gyration.

actual_Q_mul_P derives the target matrix B from the actual vertex and edge equivalences of r. rows_standard states that the source row index precedes the target column index. reindex_rows identifies the forward row matrix with counts (P e); backward_map and backward_rows identify the other factor with counts (Q e A). Both factors belong to the literal row convention.

For all n,m,d, with NeZero d and hd : 3 ∣ d, relabel_residue equates the actual relabelEdge weight in the two standard bases with the reduction of timed r gyration from ZMod d to ZMod 3. The edge bijection supplies the matrix identity; no desired equality or literal signed eight-by-eight graph matrix is an additional premise. Zero dimensions and arbitrary parallel-edge permutations remain allowed.

These constructions and identities are repository-derived. Their provenance does not assert literature novelty.

**Theorem 1.1 (reindex_rows).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelResidue.reindex_rows`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelResidue.reindex_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the standard source and target bases, the row matrix of vertex reindexing is the counted permutation factor. This fixes the orientation of the forward factor.

**Theorem 1.2 (relabel_residue).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelResidue.relabel_residue`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelResidue.relabel_residue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact requested comparison, for every finite n,m, including zero, and every nonzero d with 3 dividing d. There is no added equality premise.

**Remark 1.3 (actual_Q_mul_P).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelResidue.actual_Q_mul_P`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelResidue.actual_Q_mul_P` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This coefficient equality uses the ACTUAL edge bijection, so arbitrary parallel-edge permutations have not been discarded from the input.

**Remark 1.4 (rows_standard).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelResidue.rows_standard`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelResidue.rows_standard` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal standard-basis entries, with the ROW index first.

**Remark 1.5 (rows_right_standard).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelResidue.rows_right_standard`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelResidue.rows_right_standard` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The row matrix of right multiplication in the standard bases is the given rectangular matrix. It is used to identify the backward factor without a transpose.

**Remark 1.6 (backward_map).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelResidue.backward_map`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelResidue.backward_map` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Graph time after inverse vertex reindexing is right multiplication by the counted complementary factor Q. This identifies the actual backward linear map.

**Remark 1.7 (backward_rows).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelResidue.backward_rows`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelResidue.backward_rows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Taking standard row coordinates of backward_map yields counts of Q. Together with reindex_rows it identifies both factors in the relabel cochain.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelResidue.actual_Q_mul_P`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelResidue.backward_map`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelResidue.backward_rows`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelResidue.reindex_rows`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelResidue.relabel_residue`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelResidue.rows_right_standard`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelResidue.rows_standard`
- Dependency: [D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel](ActualRankedPermutationRelabel.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordMatrixPath](ActualWordMatrixPath.md)
