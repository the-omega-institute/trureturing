# Three-cell response-table compression

## Abstract

The fourth row probability is determined by the first three and normalization. Exact rational compression preserves the retained expectations on the original response-table carrier.

**Definition 1.1 (Actual nonzero support).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/ReducedResponseTableMoments.finiteLawSupport`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/ReducedResponseTableMoments.finiteLawSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Counts nonzero masses on the original finite carrier, rather than only the size of a latent presentation.

**Theorem 1.2 (Pushforward cannot enlarge support).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/ReducedResponseTableMoments.momentCompression_sparse_support_card_le`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/ReducedResponseTableMoments.momentCompression_sparse_support_card_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonzero sparse mass is in the image of a retained latent profile. Its support size is bounded by the profile count.

**Theorem 1.3 (Original-carrier feature preservation).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/ReducedResponseTableMoments.momentCompression_sparse_coordinate_eq`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/ReducedResponseTableMoments.momentCompression_sparse_coordinate_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Combines the existing coordinate identity with the existing original-carrier pushforward theorem.

**Definition 1.4 (Three indicators per row).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/ReducedResponseTableMoments.reducedTableFeature`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/ReducedResponseTableMoments.reducedTableFeature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reuses the established quaternary response encoding and retains digits zero, one and two.

**Theorem 1.5 (Recover the omitted fourth cell).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/ReducedResponseTableMoments.boolean_pair_law_eq_of_first_three`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/ReducedResponseTableMoments.boolean_pair_law_eq_of_first_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of three cells between two normalized response laws forces equality of the fourth cell.

**Theorem 1.6 (Bind moments to actual row distributions).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/ReducedResponseTableMoments.reducedTableFeature_moment_eq_cell`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/ReducedResponseTableMoments.reducedTableFeature_moment_eq_cell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The feature expectation is exactly a cell of the existing tableEvaluationLaw pushforward.

**Theorem 1.7 (Preserve all complete row laws).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/ReducedResponseTableMoments.reducedTableMoments_preserve_rows`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/ReducedResponseTableMoments.reducedTableMoments_preserve_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three retained expectations in each row determine its full four-cell law.

**Theorem 1.8 (At most 3k+1 atoms for all row laws).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/ReducedResponseTableMoments.exists_three_cell_table_compression`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/ReducedResponseTableMoments.exists_three_cell_table_compression` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Constructs a rational replacement law with every row marginal unchanged. Cross-row dependence is allowed to change.

**Theorem 1.9 (At most 3k+2 atoms with an additional query).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/ReducedResponseTableMoments.exists_three_cell_query_compression`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/ReducedResponseTableMoments.exists_three_cell_query_compression` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Preserves all complete row marginals and one arbitrary rational table-query expectation on the same original table carrier.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/ReducedResponseTableMoments.boolean_pair_law_eq_of_first_three`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/ReducedResponseTableMoments.exists_three_cell_query_compression`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/ReducedResponseTableMoments.exists_three_cell_table_compression`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/ReducedResponseTableMoments.finiteLawSupport`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/ReducedResponseTableMoments.momentCompression_sparse_coordinate_eq`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/ReducedResponseTableMoments.momentCompression_sparse_support_card_le`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/ReducedResponseTableMoments.reducedTableFeature`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/ReducedResponseTableMoments.reducedTableFeature_moment_eq_cell`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/ReducedResponseTableMoments.reducedTableMoments_preserve_rows`
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable](FiniteConditionalResponseTable.md)
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSparseLaw](FiniteMomentSparseLaw.md)
