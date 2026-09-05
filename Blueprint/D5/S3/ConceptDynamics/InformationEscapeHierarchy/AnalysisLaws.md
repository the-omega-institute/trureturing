# Shared-Arena Analysis Laws

## Abstract

Shared-arena capture sets support certified overlap, refinement, multiplicity-spectrum, and role-histogram analysis.

**Definition 1.1 (Occurrence capture pairs).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.capturePairs`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.capturePairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The capture set removes the singleton-kernel escape set from all ordered off-diagonal state pairs.

**Definition 1.2 (Exclusive capture vector).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.exclusiveCaptureVector`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.exclusiveCaptureVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each catalog coordinate is its peer-relative unique-capture cardinality.

**Definition 1.3 (Pairwise capture overlap).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.pairwiseCaptureOverlapPairs`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.pairwiseCaptureOverlapPairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An overlap cell is the intersection of two occurrence capture sets.

**Definition 1.4 (Pairwise overlap count).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.pairwiseCaptureOverlapCount`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.pairwiseCaptureOverlapCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The count is the exact cardinality of one overlap cell.

**Definition 1.5 (Pairwise overlap rate).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.pairwiseCaptureOverlapRate`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.pairwiseCaptureOverlapRate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact rational rate uses the common arena denominator.

**Definition 1.6 (Role-signature rate).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.roleSignatureRate`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.roleSignatureRate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact rational rate divides one role-signature count by the common arena denominator.

**Definition 1.7 (Occurrence kernel refinement).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.KernelRefines`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.KernelRefines` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finer occurrence agreement relation is pointwise contained in the coarser relation.

**Definition 1.8 (Occurrence kernel equivalence).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.KernelEquivalent`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.KernelEquivalent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two occurrence kernels are equivalent when they refine one another.

**Definition 1.9 (Kernel comparison cases).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.KernelComparison`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.KernelComparison` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four cases distinguish equality, either strict direction, and incomparability.

**Definition 1.10 (Classified kernel comparison).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.kernelComparison`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.kernelComparison` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two decidable inclusion cells determine the four-way kernel classification.

**Definition 1.11 (Refinement failure witness).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.refinementWitness`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.refinementWitness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A deterministic finite search returns a state pair witnessing a false refinement cell.

**Theorem 1.12 (No witness exactly means refinement).**

$$\operatorname{refinementWitness}(C, i, j) = \operatorname{none}() \Leftrightarrow \operatorname{KernelRefines}(C, i, j).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.refinementWitness_eq_none_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.13 (A returned refinement witness is sound).**

$$\operatorname{refinementWitness}(C, i, j) = \operatorname{some}(p) \Rightarrow \left(\operatorname{agrees}(C, i, \operatorname{fst}(p), \operatorname{snd}(p)) \land \neg\operatorname{agrees}(C, j, \operatorname{fst}(p), \operatorname{snd}(p))\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.refinementWitness_eq_some_implies` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.14 (A false cell has a deterministic witness).**

$$\exists p, \operatorname{refinementWitness}(C, i, j) = \operatorname{some}(p) \Leftrightarrow \neg\operatorname{KernelRefines}(C, i, j).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.refinementWitness_exists_iff_not_kernelRefines` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.15 (Kernel comparison carries all inclusion and witness payloads).**

$$\operatorname{kernelComparison}(C, i, j) = equal \Leftrightarrow \operatorname{KernelRefines}(C, i, j) \land \operatorname{KernelRefines}(C, j, i) \land \left(\operatorname{kernelComparison}(C, i, j) = strictlyFiner \Leftrightarrow \operatorname{KernelRefines}(C, i, j) \land \exists p, \operatorname{refinementWitness}(C, j, i) = \operatorname{some}(p) \land \left(\operatorname{kernelComparison}(C, i, j) = strictlyCoarser \Leftrightarrow \exists p, \operatorname{refinementWitness}(C, i, j) = \operatorname{some}(p) \land \operatorname{KernelRefines}(C, j, i) \land \operatorname{kernelComparison}(C, i, j) = incomparable \Leftrightarrow \exists p, \operatorname{refinementWitness}(C, i, j) = \operatorname{some}(p) \land \exists p, \operatorname{refinementWitness}(C, j, i) = \operatorname{some}(p)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.kernelComparison_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Definition 1.16 (Capture multiplicity).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureMultiplicity`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureMultiplicity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiplicity counts how many catalog occurrences capture one ordered state pair.

**Definition 1.17 (Capture-multiplicity spectrum).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureSpectrum`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureSpectrum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each bucket counts off-diagonal pairs having exactly its indexed multiplicity.

**Definition 1.18 (Multiplicity-one index).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureMultiplicityOne`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureMultiplicityOne` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A nonempty catalog has a genuine spectrum coordinate for multiplicity one.

**Definition 1.19 (Ordered distinct overlap total).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.orderedDistinctOverlapTotal`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.orderedDistinctOverlapTotal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The total sums all overlap counts over ordered distinct occurrence pairs.

**Definition 1.20 (Second factorial spectrum moment).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureSpectrumSecondFactorialMoment`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureSpectrumSecondFactorialMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The second factorial moment weights each bucket by k times k minus one.

**Definition 1.21 (Role column total).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.roleHistogramTotal`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.roleHistogramTotal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A role-signature column is summed across the entire catalog.

**Definition 1.22 (Role profile equality).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.roleProfileEq`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.roleProfileEq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two occurrences have equal role profiles when every role-signature count agrees.

**Definition 1.23 (Role histogram difference).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.roleHistogramDifference`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.roleHistogramDifference` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A signed column difference compares two catalog occurrences.

**Theorem 1.24 (Zero role difference exactly means equal counts).**

$$\operatorname{roleHistogramDifference}(C, i, j, s) = 0 \Leftrightarrow \operatorname{roleHistogram}(C, i, s) = \operatorname{roleHistogram}(C, j, s).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.roleHistogramDifference_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.25 (Role profiles agree exactly when every difference vanishes).**

$$\operatorname{roleProfileEq}(C, i, j) \Leftrightarrow \forall s, \operatorname{roleHistogramDifference}(C, i, j, s) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.roleProfileEq_iff_difference_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Definition 1.26 (Redundant occurrence indices).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.redundantIndices`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.redundantIndices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The redundant-index set contains exactly occurrences with zero unique capture.

**Definition 1.27 (Catalog redundancy).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.CatalogRedundant`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.CatalogRedundant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A catalog is redundant when at least one occurrence has zero unique capture.

**Theorem 1.28 (Unique capture is capture minus peer capture).**

$$\operatorname{uniqueCapturePairs}(C, i) = \operatorname{sdiff}(\operatorname{capturePairs}(C, i), \operatorname{biUnion}(\operatorname{erase}(\operatorname{univ}(), i), \operatorname{capturePairs}(C, j))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.uniqueCapturePairs_eq_capture_sdiff_iUnion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.29 (Unique-capture sets are pairwise disjoint).**

$$i \neq j \Rightarrow \operatorname{Disjoint}(\operatorname{uniqueCapturePairs}(C, i), \operatorname{uniqueCapturePairs}(C, j)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.uniqueCapturePairs_pairwise_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.30 (Exclusive capture is bounded by full capture).**

$$\operatorname{sum}(\operatorname{uniqueCaptureCount}(C, i)) \le \operatorname{card}(\operatorname{sdiff}(\operatorname{offDiagonalPairs}(C), \operatorname{escapePairs}(C, \operatorname{fullIndexSet}(C)))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.sum_uniqueCaptureCount_le_capturedCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.31 (Pairwise overlap is symmetric).**

$$\operatorname{pairwiseCaptureOverlapPairs}(C, i, j) = \operatorname{pairwiseCaptureOverlapPairs}(C, j, i).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.pairwiseCaptureOverlap_comm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.32 (Diagonal overlap is capture).**

$$\operatorname{pairwiseCaptureOverlapPairs}(C, i, i) = \operatorname{capturePairs}(C, i).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.pairwiseCaptureOverlap_diag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.33 (Overlap lies in both capture cells).**

$$\operatorname{pairwiseCaptureOverlapPairs}(C, i, j) \subseteq \operatorname{capturePairs}(C, i) \land \operatorname{pairwiseCaptureOverlapPairs}(C, i, j) \subseteq \operatorname{capturePairs}(C, j).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.pairwiseCaptureOverlap_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.34 (Overlap count is bounded by both capture counts).**

$$\operatorname{pairwiseCaptureOverlapCount}(C, i, j) \leq \operatorname{card}(\operatorname{capturePairs}(C, i)) \land \operatorname{pairwiseCaptureOverlapCount}(C, i, j) \leq \operatorname{card}(\operatorname{capturePairs}(C, j)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.pairwiseCaptureOverlapCount_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.35 (Kernel refinement is a preorder).**

$$\operatorname{Reflexive}(\operatorname{KernelRefines}(C)) \land \operatorname{Transitive}(\operatorname{KernelRefines}(C)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.kernelRefines_preorder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.36 (Refinement reverses capture inclusion).**

$$\operatorname{KernelRefines}(C, i, j) \Leftrightarrow \operatorname{capturePairs}(C, j) \subseteq \operatorname{capturePairs}(C, i).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.kernelRefines_iff_capturePairs_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.37 (A distinct finer peer zeros coarser unique capture).**

$$\left(i \neq j \land \operatorname{KernelRefines}(C, i, j)\right) \Rightarrow \operatorname{uniqueCapturePairs}(C, j) = \emptyset.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.kernelRefines_implies_zero_uniqueCapture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.38 (A distinct finer peer zeros coarser unique count).**

$$\left(i \neq j \land \operatorname{KernelRefines}(C, i, j)\right) \Rightarrow \operatorname{uniqueCaptureCount}(C, j) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.kernelRefines_implies_zero_uniqueCaptureCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.39 (Redundancy is existence of a zero coordinate).**

$$\operatorname{CatalogRedundant}(C) \Leftrightarrow \exists i, \operatorname{uniqueCaptureCount}(C, i) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.catalogRedundant_iff_exists_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.40 (Redundancy negates catalog irredundancy).**

$$\operatorname{CatalogRedundant}(C) \Leftrightarrow \neg\operatorname{CatalogIrredundant}(C).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.catalogRedundant_iff_not_catalogIrredundant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.41 (Irredundancy empties the redundant-index set).**

$$\operatorname{CatalogIrredundant}(C) \Leftrightarrow \operatorname{redundantIndices}(C) = \emptyset.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.catalogIrredundant_iff_redundantIndices_eq_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.42 (Spec-name redundancy equivalence).**

$$\operatorname{CatalogRedundant}(C) \Leftrightarrow \neg\operatorname{CatalogIrredundant}(C).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.catalogRedundant_iff_not_irredundant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.43 (Spectrum buckets partition the arena denominator).**

$$\operatorname{sum}(\operatorname{captureSpectrum}(C, k)) = \operatorname{card}(\operatorname{offDiagonalPairs}(C)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureSpectrum_sum_eq_denominator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.44 (Zero multiplicity is full escape).**

$$\operatorname{captureSpectrum}(C, 0) = \operatorname{card}(\operatorname{escapePairs}(C, \operatorname{fullIndexSet}(C))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureSpectrum_zero_eq_fullEscape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.45 (Multiplicity one is total exclusive capture).**

$$\operatorname{captureSpectrum}(C, \operatorname{captureMultiplicityOne}(C)) = \operatorname{sum}(\operatorname{uniqueCaptureCount}(C, i)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureSpectrum_one_eq_sum_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.46 (The first moment double-counts capture incidence).**

$$\operatorname{sum}(k \times \operatorname{captureSpectrum}(C, k)) = \operatorname{sum}(\operatorname{card}(\operatorname{capturePairs}(C, i))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureSpectrum_incidence_double_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.47 (Overlap is the second factorial moment).**

$$\operatorname{orderedDistinctOverlapTotal}(C) = \operatorname{captureSpectrumSecondFactorialMoment}(C).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.pairwiseOverlap_spectrum_doubleCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.48 (Role columns sum to exclusive capture).**

$$\operatorname{sumNonzeroSignatures}(\operatorname{roleHistogramTotal}(C, s)) = \operatorname{sum}(\operatorname{uniqueCaptureCount}(C, i)) \land \operatorname{sum}(\operatorname{uniqueCaptureCount}(C, i)) = \operatorname{captureSpectrum}(C, \operatorname{captureMultiplicityOne}(C)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.catalogRoleHistogram_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.49 (Hierarchy spectrum total).**

$$\operatorname{sum}(\operatorname{captureSpectrum}(C, k)) = \operatorname{card}(\operatorname{offDiagonalPairs}(C)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.spectrum_total` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.50 (Hierarchy zero-multiplicity bucket).**

$$\operatorname{captureSpectrum}(C, 0) = \operatorname{card}(\operatorname{escapePairs}(C, \operatorname{fullIndexSet}(C))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.spectrum_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.51 (Hierarchy multiplicity-one bucket).**

$$\operatorname{captureSpectrum}(C, \operatorname{captureMultiplicityOne}(C)) = \operatorname{sum}(\operatorname{uniqueCaptureCount}(C, i)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.spectrum_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.52 (Hierarchy first spectrum moment).**

$$\operatorname{sum}(k \times \operatorname{captureSpectrum}(C, k)) = \operatorname{sum}(\operatorname{card}(\operatorname{capturePairs}(C, i))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.spectrum_first_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.53 (Hierarchy second spectrum moment).**

$$\operatorname{captureSpectrumSecondFactorialMoment}(C) = \operatorname{orderedDistinctOverlapTotal}(C).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.spectrum_second_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.54 (Overlap symmetry and diagonal law).**

$$\operatorname{pairwiseCaptureOverlapPairs}(C, i, j) = \operatorname{pairwiseCaptureOverlapPairs}(C, j, i) \land \operatorname{pairwiseCaptureOverlapPairs}(C, i, i) = \operatorname{capturePairs}(C, i).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.overlap_symmetric_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.55 (Refinement determines overlap).**

$$\operatorname{KernelRefines}(C, i, j) \Rightarrow \left(\operatorname{capturePairs}(C, j) \subseteq \operatorname{capturePairs}(C, i) \land \operatorname{pairwiseCaptureOverlapPairs}(C, i, j) = \operatorname{capturePairs}(C, j)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.refinement_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.CatalogRedundant`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.KernelComparison`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.KernelEquivalent`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.KernelRefines`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureMultiplicity`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureMultiplicityOne`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.capturePairs`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureSpectrum`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureSpectrumSecondFactorialMoment`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureSpectrum_incidence_double_count`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureSpectrum_one_eq_sum_unique`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureSpectrum_sum_eq_denominator`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureSpectrum_zero_eq_fullEscape`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.catalogIrredundant_iff_redundantIndices_eq_empty`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.catalogRedundant_iff_exists_zero`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.catalogRedundant_iff_not_catalogIrredundant`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.catalogRedundant_iff_not_irredundant`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.catalogRoleHistogram_sum`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.exclusiveCaptureVector`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.kernelComparison`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.kernelComparison_spec`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.kernelRefines_iff_capturePairs_subset`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.kernelRefines_implies_zero_uniqueCapture`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.kernelRefines_implies_zero_uniqueCaptureCount`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.kernelRefines_preorder`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.orderedDistinctOverlapTotal`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.overlap_symmetric_diagonal`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.pairwiseCaptureOverlapCount`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.pairwiseCaptureOverlapCount_le`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.pairwiseCaptureOverlapPairs`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.pairwiseCaptureOverlapRate`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.pairwiseCaptureOverlap_comm`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.pairwiseCaptureOverlap_diag`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.pairwiseCaptureOverlap_subset`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.pairwiseOverlap_spectrum_doubleCount`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.redundantIndices`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.refinementWitness`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.refinementWitness_eq_none_iff`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.refinementWitness_eq_some_implies`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.refinementWitness_exists_iff_not_kernelRefines`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.refinement_overlap`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.roleHistogramDifference`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.roleHistogramDifference_eq_zero_iff`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.roleHistogramTotal`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.roleProfileEq`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.roleProfileEq_iff_difference_zero`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.roleSignatureRate`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.spectrum_first_moment`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.spectrum_second_moment`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.spectrum_total`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.spectrum_unique`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.spectrum_zero`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.sum_uniqueCaptureCount_le_capturedCount`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.uniqueCapturePairs_eq_capture_sdiff_iUnion`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.uniqueCapturePairs_pairwise_disjoint`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/RoleHistogram](../InformationEscape/RoleHistogram.md)
