# Generated-Kernel Hierarchy Laws

## Abstract

Hasse paths characterize chain hierarchies, strict chains obey the sharp finite bound, and E1 realizes the four-node diamond.

**Definition 1.1 (Generated-kernel cover).**

$$\operatorname{IsCover}(C, Q, P) \iff \operatorname{CovBy}(Q, P).$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/HierarchyLaws.IsCover` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A cover is the Mathlib covering relation in the generated-kernel refinement order.

**Definition 1.2 (Hasse path).**

$$\operatorname{HasHassePath}(C) \iff \operatorname{Preconnected}(\operatorname{Hasse}(C)) \land \left(\operatorname{UniqueCoverAbove}(C) \land \operatorname{UniqueCoverBelow}(C)\right).$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/HierarchyLaws.HasHassePath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Hasse graph is connected and has at most one cover above and below each node.

**Definition 1.3 (Generators comparable after closure).**

$$\operatorname{GeneratorsComparableAfterClosure}(C) \iff \operatorname{PairwiseComparableSingletonKernels}(C).$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/HierarchyLaws.GeneratorsComparableAfterClosure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every two singleton generator kernels are comparable after quotienting by exact kernel equality.

**Theorem 1.4 (Hasse paths characterize chains).**

$$(\operatorname{HasHassePath}(C) \iff \forall P, Q: \operatorname{GeneratedKernel}(C), P \le Q \lor Q \le P) \land ((\forall P, Q: \operatorname{GeneratedKernel}(C), P \le Q \lor Q \le P) \iff \operatorname{GeneratorsComparableAfterClosure}(C)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/HierarchyLaws.hasse_path_iff_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite generated lattices have path-shaped Hasse graphs exactly when every pair of nodes is comparable.

**Theorem 1.5 (Strict generator edges need not be covers).**

$$(\forall P, Q: \operatorname{GeneratedKernel}(shortcutCatalog), P \le Q \lor Q \le P) \land \left(\operatorname{StrictGeneratorStep}(shortcutCatalog, \operatorname{generatedKernel}(shortcutCatalog, \emptyset), \operatorname{generatedKernel}(shortcutCatalog, \operatorname{fullIndexSet}(shortcutCatalog)), 2) \land \neg\operatorname{IsCover}(\operatorname{generatedKernel}(shortcutCatalog, \operatorname{fullIndexSet}(shortcutCatalog)), \operatorname{generatedKernel}(shortcutCatalog, \emptyset))\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/HierarchyLaws.strict_generator_dag_shortcut_not_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A constant, first-coordinate, and identity catalog forms a chain while its direct identity step skips the middle cover level.

**Theorem 1.6 (Strict chain length is bounded by arena size).**

$$\operatorname{length}(chain) \leq \operatorname{card}(arena) - 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/HierarchyLaws.strict_chain_length_le_card_sub_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each strict step increases the finite kernel-profile range, so at most one fewer step than states is possible.

**Theorem 1.7 (Nested coarser generators have zero flat capture).**

$$\left(i \neq j \land \operatorname{generatedKernel}(C, \operatorname{singleton}(j)) \le \operatorname{generatedKernel}(C, \operatorname{singleton}(i))\right) \Rightarrow \operatorname{uniqueCapturePairs}(C, i) = \emptyset.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/HierarchyLaws.nested_flat_coarse_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The shared-arena refinement law is applied to singleton generated kernels.

**Theorem 1.8 (E1 has four extensional nodes).**

$$\operatorname{card}(e1KernelClasses) = 4 \land \left(\operatorname{card}(\operatorname{escapeAt}(\operatorname{generatedKernel}(e1Catalog, \emptyset))) = 12 \land \left(\operatorname{card}(\operatorname{escapeAt}(\operatorname{generatedKernel}(e1Catalog, \operatorname{singleton}(0)))) = 4 \land \left(\operatorname{card}(\operatorname{escapeAt}(\operatorname{generatedKernel}(e1Catalog, \operatorname{singleton}(1)))) = 4 \land \operatorname{card}(\operatorname{escapeAt}(\operatorname{generatedKernel}(e1Catalog, \operatorname{singleton}(2)))) = 0\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/HierarchyLaws.e1_four_node_escape_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Kernel reflection checks four quotient classes with escape counts twelve, four, four, and zero.

**Theorem 1.9 (E1 forms a strict diamond).**

$$\neg\operatorname{generatedKernel}(e1Catalog, \operatorname{singleton}(0)) \le \operatorname{generatedKernel}(e1Catalog, \operatorname{singleton}(1)) \land \left(\neg\operatorname{generatedKernel}(e1Catalog, \operatorname{singleton}(1)) \le \operatorname{generatedKernel}(e1Catalog, \operatorname{singleton}(0)) \land \left(\operatorname{StrictGeneratorStep}(e1Catalog, \operatorname{generatedKernel}(e1Catalog, \emptyset), \operatorname{generatedKernel}(e1Catalog, \operatorname{singleton}(0)), 0) \land \left(\operatorname{StrictGeneratorStep}(e1Catalog, \operatorname{generatedKernel}(e1Catalog, \operatorname{singleton}(0)), \operatorname{generatedKernel}(e1Catalog, \operatorname{fullIndexSet}(e1Catalog)), 1) \land \left(\operatorname{StrictGeneratorStep}(e1Catalog, \operatorname{generatedKernel}(e1Catalog, \emptyset), \operatorname{generatedKernel}(e1Catalog, \operatorname{singleton}(1)), 1) \land \left(\operatorname{StrictGeneratorStep}(e1Catalog, \operatorname{generatedKernel}(e1Catalog, \operatorname{singleton}(1)), \operatorname{generatedKernel}(e1Catalog, \operatorname{fullIndexSet}(e1Catalog)), 0) \land \operatorname{StrictGeneratorStep}(e1Catalog, \operatorname{generatedKernel}(e1Catalog, \emptyset), \operatorname{generatedKernel}(e1Catalog, \operatorname{fullIndexSet}(e1Catalog)), 2)\right)\right)\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/HierarchyLaws.e1_diamond_strict_steps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate kernels are incomparable; both coordinate paths and the direct identity shortcut are strict.

**Theorem 1.10 (E1 schedule increments).**

$$(\lambda i, \operatorname{incrementCount}(e1CoordinateSchedule, i)) = ![8, 4, 0] \land (\lambda i, \operatorname{incrementCount}(e1IdentitySchedule, i)) = ![12, 0, 0].$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/HierarchyLaws.e1_schedule_increment_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate-first and identity-first classified schedules have the two specified increment vectors.

**Theorem 1.11 (E1 flat capture and multiplicity spectrum).**

$$\operatorname{uniqueCapturePairs}(e1Catalog, 0) = \emptyset \land \left(\operatorname{uniqueCapturePairs}(e1Catalog, 1) = \emptyset \land \left(\operatorname{uniqueCapturePairs}(e1Catalog, 2) = \emptyset \land \left(\operatorname{captureSpectrum}(e1Catalog, 0) = 0 \land \left(\operatorname{captureSpectrum}(e1Catalog, 1) = 0 \land \left(\operatorname{captureSpectrum}(e1Catalog, 2) = 8 \land \operatorname{captureSpectrum}(e1Catalog, 3) = 4\right)\right)\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/HierarchyLaws.e1_unique_capture_and_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All three leave-one-out unique sets are empty and the four multiplicity buckets are zero, zero, eight, and four.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/HierarchyLaws.GeneratorsComparableAfterClosure`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/HierarchyLaws.HasHassePath`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/HierarchyLaws.IsCover`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/HierarchyLaws.e1_diamond_strict_steps`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/HierarchyLaws.e1_four_node_escape_counts`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/HierarchyLaws.e1_schedule_increment_counts`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/HierarchyLaws.e1_unique_capture_and_spectrum`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/HierarchyLaws.hasse_path_iff_chain`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/HierarchyLaws.nested_flat_coarse_zero`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/HierarchyLaws.strict_chain_length_le_card_sub_one`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/HierarchyLaws.strict_generator_dag_shortcut_not_cover`
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws](AnalysisLaws.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain](KernelChain.md)
- Dependency: [D5/S3/ConceptDynamics/Refinement/StrictRefinementBound](../Refinement/StrictRefinementBound.md)
