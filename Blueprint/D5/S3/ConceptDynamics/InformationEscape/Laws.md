# Information Escape Catalog Laws

## Abstract

Finite catalog laws for labels, primitive kernels, irredundancy, and augmentation.

**Definition 1.1 (Catalog reindexing).**

$$\operatorname{Index}(\operatorname{reindex}(C, e)) = J$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/Laws.reindex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This definition is computed from the finite catalog and its canonical primitive kernels.

**Definition 1.2 (Catalog theorem-family replacement).**

$$\operatorname{Index}(\operatorname{withTheoremAt}(C, U)) = \operatorname{Index}(C)$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/Laws.withTheoremAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This definition is computed from the finite catalog and its canonical primitive kernels.

**Theorem 1.3 (Every selected escape finset is invariant under reindexing).**

$$\forall e: \operatorname{Index}(C) \equiv J, \operatorname{escapePairs}(\operatorname{reindex}(C, e), \operatorname{map}(\operatorname{toEmbedding}(e), A)) = \operatorname{escapePairs}(C, A)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/Laws.escapePairs_reindex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses the frozen finite-kernel and exact-count APIs.

**Theorem 1.4 (Every selected escape rate is invariant under reindexing).**

$$\forall e: \operatorname{Index}(C) \equiv J, \operatorname{escapeRate}(\operatorname{reindex}(C, e), \operatorname{map}(\operatorname{toEmbedding}(e), A)) = \operatorname{escapeRate}(C, A)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/Laws.escapeRate_reindex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses the frozen finite-kernel and exact-count APIs.

**Theorem 1.5 (Unique capture is invariant under reindexing).**

$$\forall e: \operatorname{Index}(C) \equiv J, \operatorname{uniqueCaptureCount}(\operatorname{reindex}(C, e), \operatorname{apply}(e, i)) = \operatorname{uniqueCaptureCount}(C, i)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/Laws.uniqueCaptureCount_reindex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses the frozen finite-kernel and exact-count APIs.

**Theorem 1.6 (Exact theorem gain is invariant under reindexing).**

$$\forall e: \operatorname{Index}(C) \equiv J, \operatorname{theoremGainRate}(\operatorname{reindex}(C, e), \operatorname{apply}(e, i)) = \operatorname{theoremGainRate}(C, i)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/Laws.theoremGainRate_reindex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses the frozen finite-kernel and exact-count APIs.

**Theorem 1.7 (Pointwise kernel equality preserves every unique capture count).**

$$(\forall j, x, y, \operatorname{relation}(\operatorname{toKernel}(\operatorname{primitives}(\operatorname{theoremAt}(C, j))), x, y) \Leftrightarrow \operatorname{relation}(\operatorname{toKernel}(\operatorname{primitives}(\operatorname{apply}(U, j))), x, y)) \Rightarrow \operatorname{uniqueCaptureCount}(\operatorname{withTheoremAt}(C, U), i) = \operatorname{uniqueCaptureCount}(C, i)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/Laws.uniqueCaptureCount_congr_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses the frozen finite-kernel and exact-count APIs.

**Theorem 1.8 (Pointwise kernel equality preserves every unique capture finset).**

$$(\forall j, x, y, \operatorname{relation}(\operatorname{toKernel}(\operatorname{primitives}(\operatorname{theoremAt}(C, j))), x, y) \Leftrightarrow \operatorname{relation}(\operatorname{toKernel}(\operatorname{primitives}(\operatorname{apply}(U, j))), x, y)) \Rightarrow \operatorname{uniqueCapturePairs}(\operatorname{withTheoremAt}(C, U), i) = \operatorname{uniqueCapturePairs}(C, i)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/Laws.uniqueCapturePairs_congr_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses the frozen finite-kernel and exact-count APIs.

**Theorem 1.9 (Pointwise kernel equality preserves full-catalog escape pairs).**

$$(\forall j, x, y, \operatorname{relation}(\operatorname{toKernel}(\operatorname{primitives}(\operatorname{theoremAt}(C, j))), x, y) \Leftrightarrow \operatorname{relation}(\operatorname{toKernel}(\operatorname{primitives}(\operatorname{apply}(U, j))), x, y)) \Rightarrow \operatorname{escapePairs}(\operatorname{withTheoremAt}(C, U), \operatorname{fullIndexSet}(\operatorname{withTheoremAt}(C, U))) = \operatorname{escapePairs}(C, \operatorname{fullIndexSet}(C))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/Laws.escapePairs_congr_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses the frozen finite-kernel and exact-count APIs.

**Theorem 1.10 (Pointwise kernel equality preserves the full-catalog escape count).**

$$(\forall j, x, y, \operatorname{relation}(\operatorname{toKernel}(\operatorname{primitives}(\operatorname{theoremAt}(C, j))), x, y) \Leftrightarrow \operatorname{relation}(\operatorname{toKernel}(\operatorname{primitives}(\operatorname{apply}(U, j))), x, y)) \Rightarrow \operatorname{card}(\operatorname{escapePairs}(\operatorname{withTheoremAt}(C, U), \operatorname{fullIndexSet}(\operatorname{withTheoremAt}(C, U)))) = \operatorname{card}(\operatorname{escapePairs}(C, \operatorname{fullIndexSet}(C)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/Laws.escapeCount_congr_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses the frozen finite-kernel and exact-count APIs.

**Theorem 1.11 (Pointwise kernel equality preserves the full-catalog escape rate).**

$$(\forall j, x, y, \operatorname{relation}(\operatorname{toKernel}(\operatorname{primitives}(\operatorname{theoremAt}(C, j))), x, y) \Leftrightarrow \operatorname{relation}(\operatorname{toKernel}(\operatorname{primitives}(\operatorname{apply}(U, j))), x, y)) \Rightarrow \operatorname{escapeRate}(\operatorname{withTheoremAt}(C, U), \operatorname{fullIndexSet}(\operatorname{withTheoremAt}(C, U))) = \operatorname{escapeRate}(C, \operatorname{fullIndexSet}(C))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/Laws.escapeRate_congr_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses the frozen finite-kernel and exact-count APIs.

**Theorem 1.12 (Kernel-equivalent primitive realizations have identical counts).**

$$(\forall x, y, \operatorname{agrees}(\operatorname{toPrimitiveBundle}(R), x, y) \Leftrightarrow \operatorname{agrees}(\operatorname{toPrimitiveBundle}(S), x, y)) \Rightarrow \operatorname{uniqueCaptureCount}(\operatorname{withTheoremAt}(C, (j \mapsto \operatorname{ite}(j = k, \operatorname{TheoremUnit}(\operatorname{toPrimitiveBundle}(R), \operatorname{Statement}(\operatorname{theoremAt}(C, j)), \operatorname{proof}(\operatorname{theoremAt}(C, j))), \operatorname{theoremAt}(C, j)))), i) = \operatorname{uniqueCaptureCount}(\operatorname{withTheoremAt}(C, (j \mapsto \operatorname{ite}(j = k, \operatorname{TheoremUnit}(\operatorname{toPrimitiveBundle}(S), \operatorname{Statement}(\operatorname{theoremAt}(C, j)), \operatorname{proof}(\operatorname{theoremAt}(C, j))), \operatorname{theoremAt}(C, j)))), i)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/Laws.uniqueCaptureCount_congr_primitiveRealization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses the frozen finite-kernel and exact-count APIs.

**Definition 1.13 (Catalog irredundancy).**

$$\operatorname{CatalogIrredundant}(C) = \forall i, \operatorname{LowersEscape}(C, i)$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/Laws.CatalogIrredundant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This definition is computed from the finite catalog and its canonical primitive kernels.

**Theorem 1.14 (Irredundancy is positivity of all unique captures).**

$$\operatorname{CatalogIrredundant}(C) \Leftrightarrow \forall i, 0 < \operatorname{uniqueCaptureCount}(C, i)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/Laws.catalogIrredundant_iff_forall_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses the frozen finite-kernel and exact-count APIs.

**Definition 1.15 (Augmented theorem statement).**

$$\operatorname{AugmentedStatement}(C, i) = \operatorname{And}(\operatorname{Statement}(\operatorname{theoremAt}(C, i)), \operatorname{LowersEscape}(C, i))$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/Laws.AugmentedStatement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This definition is computed from the finite catalog and its canonical primitive kernels.

**Theorem 1.16 (Augmented theorem proof constructor).**

$$\operatorname{LowersEscape}(C, i) \Rightarrow \operatorname{AugmentedStatement}(C, i)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/Laws.augmentedProof` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses the frozen finite-kernel and exact-count APIs.

**Theorem 1.17 (Every theorem in an irredundant catalog is augmented).**

$$\operatorname{CatalogIrredundant}(C) \Rightarrow \forall i, \operatorname{AugmentedStatement}(C, i)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/Laws.catalog_all_augmented` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses the frozen finite-kernel and exact-count APIs.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/Laws.AugmentedStatement`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/Laws.CatalogIrredundant`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/Laws.augmentedProof`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/Laws.catalogIrredundant_iff_forall_pos`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/Laws.catalog_all_augmented`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/Laws.escapeCount_congr_kernel`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/Laws.escapePairs_congr_kernel`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/Laws.escapePairs_reindex`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/Laws.escapeRate_congr_kernel`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/Laws.escapeRate_reindex`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/Laws.reindex`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/Laws.theoremGainRate_reindex`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/Laws.uniqueCaptureCount_congr_kernel`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/Laws.uniqueCaptureCount_congr_primitiveRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/Laws.uniqueCaptureCount_reindex`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/Laws.uniqueCapturePairs_congr_kernel`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/Laws.withTheoremAt`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/ExactRate](ExactRate.md)
