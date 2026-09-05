# Layered Capture

## Abstract

Certified kernel chains partition a finite arena into ordered captures and a final unresolved set.

**Definition 1.1 (Catalog identity).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.CatalogId`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.CatalogId` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A catalog projection has a stable Lean name.

**Definition 1.2 (Catalog kind).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.CatalogKind`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.CatalogKind` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Catalogs are classified as canonical maximal families or bounded analysis views.

**Definition 1.3 (Catalog occurrence).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.CatalogOccurrence`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.CatalogOccurrence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An occurrence records root, catalog, arena, theorem, unit, realization, and theorem-unit identities.

**Definition 1.4 (Maximal catalog assembly).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.maximalCatalog`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.maximalCatalog` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Assembly retains the canonical occurrences matching one root and one object arena.

**Definition 1.5 (Certified layer chain).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.LayerChain`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.LayerChain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every adjacent kernel carries a proof that the later relation refines the earlier relation.

**Definition 1.6 (Layered capture pairs).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.layeredCapturePairs`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.layeredCapturePairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Layer zero contains pairs separated by the first kernel; successor layers contain pairs removed by one refinement.

**Definition 1.7 (Layered capture count).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.layeredCaptureCount`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.layeredCaptureCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The count is the cardinality of one layered capture set.

**Definition 1.8 (Layered capture spectrum).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.layeredCaptureSpectrum`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.layeredCaptureSpectrum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The spectrum lists the capture count at every ordered layer.

**Definition 1.9 (Layered capture rate).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.layeredCaptureRate`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.layeredCaptureRate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each exact rate divides its layer count by the arena's off-diagonal denominator.

**Definition 1.10 (Unresolved pairs).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.unresolvedPairs`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.unresolvedPairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The unresolved set contains off-diagonal pairs related by the final kernel.

**Definition 1.11 (Unresolved count).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.unresolvedCount`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.unresolvedCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The unresolved count is the cardinality of the final unresolved set.

**Definition 1.12 (Unresolved rate).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.unresolvedRate`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.unresolvedRate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact unresolved rate uses the same arena denominator as every layer.

**Theorem 1.13 (Initial capture nonemptiness).**

$$\operatorname{Nonempty}(\operatorname{layeredCapturePairs}(C, \operatorname{zero}())) \Leftrightarrow \exists x, y, x \neq y \land \neg\operatorname{relation}(\operatorname{kernel}(C, \operatorname{zero}()), x, y).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.layeredCapture_zero_nonempty_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from the typed chain data and finite kernel-set algebra.

**Theorem 1.14 (Initial capture is failure of off-diagonal containment).**

$$\operatorname{Nonempty}(\operatorname{layeredCapturePairs}(C, \operatorname{zero}())) \Leftrightarrow \neg(\operatorname{coe}(\operatorname{offDiagonalPairs}(\operatorname{State}(arena))) \subseteq \operatorname{setOf}(p, \operatorname{relation}(\operatorname{kernel}(C, \operatorname{zero}()), \operatorname{fst}(p), \operatorname{snd}(p)))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.layeredCapture_zero_nonempty_iff_not_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from the typed chain data and finite kernel-set algebra.

**Theorem 1.15 (Successor capture nonemptiness).**

$$\operatorname{Nonempty}(\operatorname{layeredCapturePairs}(C, \operatorname{succ}(r))) \Leftrightarrow \exists x, y, \operatorname{relation}(\operatorname{kernel}(C, \operatorname{castSucc}(r)), x, y) \land \neg\operatorname{relation}(\operatorname{kernel}(C, \operatorname{succ}(r)), x, y).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.layeredCapture_succ_nonempty_iff_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from the typed chain data and finite kernel-set algebra.

**Theorem 1.16 (Layered capture partition).**

$$(\forall r, s: \operatorname{Fin}(\operatorname{length}(C) + 1), r \neq s \Rightarrow \operatorname{Disjoint}(\operatorname{layeredCapturePairs}(C, r), \operatorname{layeredCapturePairs}(C, s))) \land \left((\forall r: \operatorname{Fin}(\operatorname{length}(C) + 1), \operatorname{Disjoint}(\operatorname{layeredCapturePairs}(C, r), \operatorname{unresolvedPairs}(C))) \land \operatorname{union}(\operatorname{biUnion}(\operatorname{univ}(), \operatorname{layeredCapturePairs}(C)), \operatorname{unresolvedPairs}(C)) = \operatorname{offDiagonalPairs}(\operatorname{State}(arena))\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.layeredCapture_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from the typed chain data and finite kernel-set algebra.

**Theorem 1.17 (Strict refinement is nonempty capture).**

$$(\operatorname{relation}(\operatorname{kernel}(C, \operatorname{succ}(r))) \le \operatorname{relation}(\operatorname{kernel}(C, \operatorname{castSucc}(r))) \land \neg(\operatorname{relation}(\operatorname{kernel}(C, \operatorname{castSucc}(r))) \le \operatorname{relation}(\operatorname{kernel}(C, \operatorname{succ}(r))))) \Leftrightarrow \operatorname{Nonempty}(\operatorname{layeredCapturePairs}(C, \operatorname{succ}(r))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.strictRefinement_iff_layeredCapture_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from the typed chain data and finite kernel-set algebra.

**Theorem 1.18 (A finer peer zeros coarser unique capture).**

$$\left(i \neq j \land \operatorname{KernelRefines}(A, i, j)\right) \Rightarrow \operatorname{uniqueCapturePairs}(A, j) = \emptyset.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.cumulativeChain_coarser_uniqueCapture_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from the typed chain data and finite kernel-set algebra.

**Definition 1.19 (Packed catalog).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.PackedCatalog`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.PackedCatalog` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A packed catalog stores an arena together with a catalog definitionally over that arena.

**Definition 1.20 (Designated root catalog suite).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.DesignatedRootCatalogSuite`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.DesignatedRootCatalogSuite` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite dependent catalogAt family lists every maximal catalog owned by one sealing root.

**Definition 1.21 (System catalog irredundancy).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.SystemCatalogIrredundant`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.SystemCatalogIrredundant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every maximal catalog in the designated root must be irredundant.

**Definition 1.22 (System-wide positivity).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.SystemWidePositive`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.SystemWidePositive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The compatibility name denotes the same one-root universal proposition.

**Theorem 1.23 (System positivity is designated-root irredundancy).**

$$\operatorname{SystemWidePositive}(S) \Leftrightarrow \operatorname{SystemCatalogIrredundant}(S).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.systemWidePositive_iff_systemCatalogIrredundant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from the typed chain data and finite kernel-set algebra.

**Definition 1.24 (Generated schedule layer chain).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.toLayerChain`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.toLayerChain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A classified generator schedule yields a certified general kernel chain.

**Theorem 1.25 (Generated layered captures are schedule increments).**

$$\operatorname{layeredCapturePairs}(\operatorname{toLayerChain}(G), \operatorname{succ}(r)) = \operatorname{increment}(G, r).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.toLayerChain_layeredCapture_succ_eq_increment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from the typed chain data and finite kernel-set algebra.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.CatalogId`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.CatalogKind`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.CatalogOccurrence`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.DesignatedRootCatalogSuite`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.LayerChain`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.PackedCatalog`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.SystemCatalogIrredundant`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.SystemWidePositive`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.cumulativeChain_coarser_uniqueCapture_zero`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.layeredCaptureCount`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.layeredCapturePairs`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.layeredCaptureRate`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.layeredCaptureSpectrum`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.layeredCapture_partition`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.layeredCapture_succ_nonempty_iff_strict`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.layeredCapture_zero_nonempty_iff`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.layeredCapture_zero_nonempty_iff_not_subset`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.maximalCatalog`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.strictRefinement_iff_layeredCapture_nonempty`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.systemWidePositive_iff_systemCatalogIrredundant`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.toLayerChain`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.toLayerChain_layeredCapture_succ_eq_increment`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.unresolvedCount`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.unresolvedPairs`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.unresolvedRate`
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws](AnalysisLaws.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain](KernelChain.md)
