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

**Theorem 1.3 (Unique capture is invariant under reindexing).**

$$\operatorname{uniqueCaptureCount}(\operatorname{reindex}(C, e), \operatorname{apply}(e, i)) = \operatorname{uniqueCaptureCount}(C, i)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/Laws.uniqueCaptureCount_reindex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses the frozen finite-kernel and exact-count APIs.

**Theorem 1.4 (Exact theorem gain is invariant under reindexing).**

$$\operatorname{theoremGainRate}(\operatorname{reindex}(C, e), \operatorname{apply}(e, i)) = \operatorname{theoremGainRate}(C, i)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/Laws.theoremGainRate_reindex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses the frozen finite-kernel and exact-count APIs.

**Theorem 1.5 (Pointwise kernel equality preserves every unique capture count).**

$$\operatorname{PointwiseKernelEqual}(C, U) \Rightarrow \operatorname{uniqueCaptureCount}(\operatorname{withTheoremAt}(C, U), i) = \operatorname{uniqueCaptureCount}(C, i)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/Laws.uniqueCaptureCount_congr_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses the frozen finite-kernel and exact-count APIs.

**Theorem 1.6 (Kernel-equivalent primitive realizations have identical counts).**

$$\operatorname{AgreementEqual}(R, S) \Rightarrow \operatorname{uniqueCaptureCount}(\operatorname{replace}(C, R), i) = \operatorname{uniqueCaptureCount}(\operatorname{replace}(C, S), i)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/Laws.uniqueCaptureCount_congr_primitiveRealization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses the frozen finite-kernel and exact-count APIs.

**Definition 1.7 (Catalog irredundancy).**

$$\operatorname{CatalogIrredundant}(C) = \forall i, \operatorname{LowersEscape}(C, i)$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/Laws.CatalogIrredundant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This definition is computed from the finite catalog and its canonical primitive kernels.

**Theorem 1.8 (Irredundancy is positivity of all unique captures).**

$$\operatorname{CatalogIrredundant}(C) \Leftrightarrow \forall i, 0 < \operatorname{uniqueCaptureCount}(C, i)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/Laws.catalogIrredundant_iff_forall_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses the frozen finite-kernel and exact-count APIs.

**Definition 1.9 (Augmented theorem statement).**

$$\operatorname{AugmentedStatement}(C, i) = \operatorname{And}(\operatorname{Statement}(C, i), \operatorname{LowersEscape}(C, i))$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/Laws.AugmentedStatement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This definition is computed from the finite catalog and its canonical primitive kernels.

**Definition 1.10 (Augmented theorem proof constructor).**

$$\operatorname{LowersEscape}(C, i) \Rightarrow \operatorname{AugmentedStatement}(C, i)$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/Laws.augmentedProof` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This definition is computed from the finite catalog and its canonical primitive kernels.

**Theorem 1.11 (Every theorem in an irredundant catalog is augmented).**

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
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/Laws.reindex`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/Laws.theoremGainRate_reindex`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/Laws.uniqueCaptureCount_congr_kernel`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/Laws.uniqueCaptureCount_congr_primitiveRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/Laws.uniqueCaptureCount_reindex`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/Laws.withTheoremAt`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty](StructuralNovelty.md)
