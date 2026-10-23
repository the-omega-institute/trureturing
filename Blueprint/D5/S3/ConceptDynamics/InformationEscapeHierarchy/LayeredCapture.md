# Layered Capture

## Abstract

Certified kernel chains partition a finite arena into ordered captures and a final unresolved set.

A finite native instance has State=Window, all five initialized one-window histories. The reader ImmediateWindowStateCapacity.rawMachine(0) starts with seam false and composition zero. Each letter carries its actual derived continuation state. The catalog consists of four singleton bundles: atom identity, the actual post-first-window seam, acceptance of the same-state high suffix, and its total Option integer reply. The last field includes none for rejection. NullReplyFiber.native_execution supplies the natural-history realization; the first and suffix states are evaluations of [a] and [a,high] by the same reader. Information kernels and proof escape remain distinct contracts.

In the order null, low, high, ends, middle the first quantities are 0,2,5,7,3; the new seams are false,true,false,true,false; the high-suffix replies are some(5),none,some(26),none,some(18). Initial acceptance is constant true. Suffix acceptance is the complement of the new seam. The joint code (atom,seam,guard,reply) is injective, so the complete catalog has zero escape. Removing atom leaves exactly (low,ends) and (ends,low). The atom unique count is two, and every other unique count is zero. With N=5 the ordered denominator is N*(N-1)=20, giving atom gain 1/10. Catalog.theoremGainRate_eq gives the leave-one-out rate identity, and the FusedCorrectness full, unique and without identities apply to the complete five-letter enumeration.

The sixteen selections generate exactly four relation-extensional nodes: total indistinguishability, the seam partition, the suffix-reply partition, and equality. Guard and seam generate the same node. The seam partition has blocks of size three and two, leaving eight ordered distinct pairs; the reply partition leaves only the two low/ends pairs. For the schedule seam,guard,reply,atom, with an explicit empty-selection initial kernel, layeredCaptureSpectrum is (0,12,0,6,2) and the final unresolved count is zero. The initial zero is this library's capture before the first listed kernel. Successor layer j is the transition from K(j-1) to K(j); the collapsed guard addition is kept with count zero. An atom-first schedule captures all twenty pairs at its first successor and all later additions collapse. LayerChain.layeredCapture_partition assigns each off-diagonal pair to its first separating layer or to the final unresolved set.

Exact rates require a finite arena with at least two states. The formulas do not assign a finite rate to an unbounded history domain; a zero denominator calls for a degenerate-domain disposition. The finite letter alphabet does not make the family of all real probability laws a finite arena. Geometry, generated kernel refinement, information capture, proof content and acquisition cost remain different objects. Zero unique capture is a catalog fact and says nothing by itself about proof substance or research value.

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
