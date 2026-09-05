# Structural Escape Novelty

## Abstract

Finite escape reduction is canonical strict kernel novelty of quotient CUTs.

**Definition 1.1 (Structural escape reduction).**

$$\operatorname{StructurallyLowersEscape}(C, i) \Leftrightarrow \operatorname{StrictSubset}(\operatorname{catalogJointKernel}(C, \operatorname{univ}()), \operatorname{catalogJointKernel}(C, \operatorname{setOf}(j \mid j \neq i))).$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty.StructurallyLowersEscape` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This definition packages the catalog kernel or its canonical quotient CUT.

**Theorem 1.2 (Structural and exact reduction agree).**

$$\operatorname{Nondegenerate}(A) \Rightarrow \operatorname{StructurallyLowersEscape}(C, i) \Leftrightarrow \operatorname{LowersEscape}(C, i).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty.structurallyLowersEscape_iff_lowersEscape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof preserves bundle kernels and reuses the canonical semantic closure.

**Definition 1.3 (Leave-one-out kernel closure).**

$$\operatorname{semanticClosureWithout}(C, i) = \operatorname{setOf}(K \mid \forall x, y, (\forall j, j \neq i \Rightarrow \operatorname{agrees}(\operatorname{theoremAt}(C, j), x, y)) \Rightarrow \operatorname{related}(K, x, y)).$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty.semanticClosureWithout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This definition packages the catalog kernel or its canonical quotient CUT.

**Definition 1.4 (Tagged quotient output).**

$$\operatorname{QuotientOutput}(C) = \operatorname{Sigma}(j, \operatorname{Quotient}(\operatorname{toKernel}(\operatorname{primitives}(\operatorname{theoremAt}(C, j))))).$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty.QuotientOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This definition packages the catalog kernel or its canonical quotient CUT.

**Definition 1.5 (Tagged canonical quotient CUT).**

$$\operatorname{taggedQuotientCut}(C, i) = \lambda x, \operatorname{tag}(i, \operatorname{quotientCut}(\operatorname{toKernel}(\operatorname{primitives}(\operatorname{theoremAt}(C, i))), x)).$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty.taggedQuotientCut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This definition packages the catalog kernel or its canonical quotient CUT.

**Definition 1.6 (Homogeneous leave-one-out CUT family).**

$$\operatorname{quotientCutsWithout}(C, i) = \operatorname{image}(\lambda j, \operatorname{taggedQuotientCut}(C, j), \operatorname{setOf}(j \mid j \neq i)).$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty.quotientCutsWithout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This definition packages the catalog kernel or its canonical quotient CUT.

**Theorem 1.7 (Catalog and canonical closures agree).**

$$\operatorname{taggedQuotientCut}(C, i) \in \operatorname{SemanticClosure}(\operatorname{quotientCutsWithout}(C, i)) \Leftrightarrow \operatorname{toKernel}(\operatorname{primitives}(\operatorname{theoremAt}(C, i))) \in \operatorname{semanticClosureWithout}(C, i).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty.taggedQuotientCut_mem_semanticClosure_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof preserves bundle kernels and reuses the canonical semantic closure.

**Theorem 1.8 (Canonical strict novelty criterion).**

$$\operatorname{Nondegenerate}(A) \Rightarrow \operatorname{LowersEscape}(C, i) \Leftrightarrow \operatorname{StrictSubset}(\operatorname{jointKernel}(\lambda d: \operatorname{insert}(\operatorname{taggedQuotientCut}(C, i), \operatorname{quotientCutsWithout}(C, i)), \operatorname{readout}(d)), \operatorname{jointKernel}(\lambda d: \operatorname{quotientCutsWithout}(C, i), \operatorname{readout}(d))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty.lowersEscape_iff_strict_kernel_novelty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof preserves bundle kernels and reuses the canonical semantic closure.

**Theorem 1.9 (Semantic closure criterion).**

$$\operatorname{Nondegenerate}(A) \Rightarrow \operatorname{LowersEscape}(C, i) \Leftrightarrow \neg(\operatorname{toKernel}(\operatorname{primitives}(\operatorname{theoremAt}(C, i))) \in \operatorname{semanticClosureWithout}(C, i)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty.lowersEscape_iff_not_mem_semanticClosureWithout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof preserves bundle kernels and reuses the canonical semantic closure.

**Theorem 1.10 (Recoverability prevents reduction).**

$$\forall x, y, (\forall j, j \neq i \Rightarrow \operatorname{agrees}(\operatorname{theoremAt}(C, j), x, y)) \Rightarrow \operatorname{agrees}(\operatorname{theoremAt}(C, i), x, y) \Rightarrow \neg\operatorname{LowersEscape}(C, i).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty.lowersEscape_false_of_recoverable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof preserves bundle kernels and reuses the canonical semantic closure.

**Theorem 1.11 (Duplicate kernels have zero capture).**

$$i \neq j \land (\forall x, y, \operatorname{agrees}(\operatorname{theoremAt}(C, i), x, y) \Leftrightarrow \operatorname{agrees}(\operatorname{theoremAt}(C, j), x, y)) \Rightarrow \operatorname{uniqueCaptureCount}(C, i) = 0 \land \operatorname{uniqueCaptureCount}(C, j) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty.same_kernel_both_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof preserves bundle kernels and reuses the canonical semantic closure.

**Theorem 1.12 (Constant kernels have zero capture).**

$$\forall x, y, \operatorname{agrees}(\operatorname{theoremAt}(C, i), x, y) \Rightarrow \operatorname{uniqueCaptureCount}(C, i) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty.constant_kernel_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof preserves bundle kernels and reuses the canonical semantic closure.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty.QuotientOutput`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty.StructurallyLowersEscape`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty.constant_kernel_zero`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty.lowersEscape_false_of_recoverable`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty.lowersEscape_iff_not_mem_semanticClosureWithout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty.lowersEscape_iff_strict_kernel_novelty`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty.quotientCutsWithout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty.same_kernel_both_zero`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty.semanticClosureWithout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty.structurallyLowersEscape_iff_lowersEscape`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty.taggedQuotientCut`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty.taggedQuotientCut_mem_semanticClosure_iff`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeLaws/StrictKernelNoveltyCriterion](../DefinitionEscapeLaws/StrictKernelNoveltyCriterion.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/ExactRate](ExactRate.md)
