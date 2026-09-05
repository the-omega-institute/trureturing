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

**Definition 1.9 (Capture multiplicity).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureMultiplicity`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureMultiplicity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiplicity counts how many catalog occurrences capture one ordered state pair.

**Definition 1.10 (Capture-multiplicity spectrum).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureSpectrum`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureSpectrum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each bucket counts off-diagonal pairs having exactly its indexed multiplicity.

**Definition 1.11 (Multiplicity-one index).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureMultiplicityOne`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureMultiplicityOne` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A nonempty catalog has a genuine spectrum coordinate for multiplicity one.

**Definition 1.12 (Ordered distinct overlap total).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.orderedDistinctOverlapTotal`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.orderedDistinctOverlapTotal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The total sums all overlap counts over ordered distinct occurrence pairs.

**Definition 1.13 (Second factorial spectrum moment).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureSpectrumSecondFactorialMoment`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureSpectrumSecondFactorialMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The second factorial moment weights each bucket by k times k minus one.

**Definition 1.14 (Role column total).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.roleHistogramTotal`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.roleHistogramTotal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A role-signature column is summed across the entire catalog.

**Definition 1.15 (Role profile equality).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.roleProfileEq`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.roleProfileEq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two occurrences have equal role profiles when every role-signature count agrees.

**Definition 1.16 (Role histogram difference).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.roleHistogramDifference`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.roleHistogramDifference` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A signed column difference compares two catalog occurrences.

**Theorem 1.17 (Zero role difference exactly means equal counts).**

$$\operatorname{roleHistogramDifference}(C, i, j, s) = 0 \Leftrightarrow \operatorname{roleHistogram}(C, i, s) = \operatorname{roleHistogram}(C, j, s).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.roleHistogramDifference_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.18 (Role profiles agree exactly when every difference vanishes).**

$$\operatorname{roleProfileEq}(C, i, j) \Leftrightarrow \forall s, \operatorname{roleHistogramDifference}(C, i, j, s) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.roleProfileEq_iff_difference_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Definition 1.19 (Redundant occurrence indices).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.redundantIndices`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.redundantIndices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The redundant-index set contains exactly occurrences with zero unique capture.

**Definition 1.20 (Catalog redundancy).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.CatalogRedundant`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.CatalogRedundant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A catalog is redundant when at least one occurrence has zero unique capture.

**Theorem 1.21 (Unique capture is capture minus peer capture).**

$$\operatorname{uniqueCapturePairs}(C, i) = \operatorname{sdiff}(\operatorname{capturePairs}(C, i), \operatorname{biUnion}(\operatorname{erase}(\operatorname{univ}(), i), \lambda j, \operatorname{capturePairs}(C, j))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.uniqueCapturePairs_eq_capture_sdiff_iUnion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.22 (Unique-capture sets are pairwise disjoint).**

$$i \neq j \Rightarrow \operatorname{Disjoint}(\operatorname{uniqueCapturePairs}(C, i), \operatorname{uniqueCapturePairs}(C, j)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.uniqueCapturePairs_pairwise_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.23 (Exclusive capture is bounded by full capture).**

$$\sum_{i} \operatorname{uniqueCaptureCount}(C, i) \le \operatorname{card}(\operatorname{sdiff}(\operatorname{offDiagonalPairs}(\operatorname{State}(A)), \operatorname{escapePairs}(C, \operatorname{fullIndexSet}(C)))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.sum_uniqueCaptureCount_le_capturedCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.24 (Pairwise overlap is symmetric).**

$$\operatorname{pairwiseCaptureOverlapPairs}(C, i, j) = \operatorname{pairwiseCaptureOverlapPairs}(C, j, i).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.pairwiseCaptureOverlap_comm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.25 (Diagonal overlap is capture).**

$$\operatorname{pairwiseCaptureOverlapPairs}(C, i, i) = \operatorname{capturePairs}(C, i).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.pairwiseCaptureOverlap_diag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.26 (Overlap lies in both capture cells).**

$$\operatorname{pairwiseCaptureOverlapPairs}(C, i, j) \subseteq \operatorname{capturePairs}(C, i) \land \operatorname{pairwiseCaptureOverlapPairs}(C, i, j) \subseteq \operatorname{capturePairs}(C, j).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.pairwiseCaptureOverlap_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.27 (Overlap count is bounded by both capture counts).**

$$\operatorname{pairwiseCaptureOverlapCount}(C, i, j) \leq \operatorname{card}(\operatorname{capturePairs}(C, i)) \land \operatorname{pairwiseCaptureOverlapCount}(C, i, j) \leq \operatorname{card}(\operatorname{capturePairs}(C, j)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.pairwiseCaptureOverlapCount_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.28 (Kernel refinement is a preorder).**

$$(\forall i, \operatorname{KernelRefines}(C, i, i)) \land (\forall i, j, k, \operatorname{KernelRefines}(C, i, j) \Rightarrow \left(\operatorname{KernelRefines}(C, j, k) \Rightarrow \operatorname{KernelRefines}(C, i, k)\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.kernelRefines_preorder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.29 (Refinement reverses capture inclusion).**

$$\operatorname{KernelRefines}(C, i, j) \Leftrightarrow \operatorname{capturePairs}(C, j) \subseteq \operatorname{capturePairs}(C, i).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.kernelRefines_iff_capturePairs_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.30 (A distinct finer peer zeros coarser unique capture).**

$$\left(i \neq j \land \operatorname{KernelRefines}(C, i, j)\right) \Rightarrow \operatorname{uniqueCapturePairs}(C, j) = \emptyset.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.kernelRefines_implies_zero_uniqueCapture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.31 (A distinct finer peer zeros coarser unique count).**

$$\left(i \neq j \land \operatorname{KernelRefines}(C, i, j)\right) \Rightarrow \operatorname{uniqueCaptureCount}(C, j) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.kernelRefines_implies_zero_uniqueCaptureCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.32 (Redundancy is existence of a zero coordinate).**

$$\operatorname{CatalogRedundant}(C) \Leftrightarrow \exists i, \operatorname{uniqueCaptureCount}(C, i) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.catalogRedundant_iff_exists_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.33 (Redundancy negates catalog irredundancy).**

$$\operatorname{CatalogRedundant}(C) \Leftrightarrow \neg\operatorname{CatalogIrredundant}(C).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.catalogRedundant_iff_not_catalogIrredundant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.34 (Irredundancy empties the redundant-index set).**

$$\operatorname{CatalogIrredundant}(C) \Leftrightarrow \operatorname{redundantIndices}(C) = \emptyset.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.catalogIrredundant_iff_redundantIndices_eq_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.35 (Spec-name redundancy equivalence).**

$$\operatorname{CatalogRedundant}(C) \Leftrightarrow \neg\operatorname{CatalogIrredundant}(C).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.catalogRedundant_iff_not_irredundant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.36 (Spectrum buckets partition the arena denominator).**

$$\sum_{k} \operatorname{captureSpectrum}(C, k) = \operatorname{card}(\operatorname{offDiagonalPairs}(\operatorname{State}(A))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureSpectrum_sum_eq_denominator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.37 (Zero multiplicity is full escape).**

$$\operatorname{captureSpectrum}(C, 0) = \operatorname{card}(\operatorname{escapePairs}(C, \operatorname{fullIndexSet}(C))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureSpectrum_zero_eq_fullEscape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.38 (Multiplicity one is total exclusive capture).**

$$\operatorname{captureSpectrum}(C, \operatorname{captureMultiplicityOne}(C)) = \sum_{i} \operatorname{uniqueCaptureCount}(C, i).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureSpectrum_one_eq_sum_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.39 (The first moment double-counts capture incidence).**

$$\sum_{k} k \times \operatorname{captureSpectrum}(C, k) = \sum_{i} \operatorname{card}(\operatorname{capturePairs}(C, i)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.captureSpectrum_incidence_double_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.40 (Overlap is the second factorial moment).**

$$\operatorname{orderedDistinctOverlapTotal}(C) = \operatorname{captureSpectrumSecondFactorialMoment}(C).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.pairwiseOverlap_spectrum_doubleCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.41 (Role columns sum to exclusive capture).**

$$\sum_{s with s \neq (\lambda b, false)} \operatorname{roleHistogramTotal}(C, s) = \sum_{i} \operatorname{uniqueCaptureCount}(C, i) \land \sum_{i} \operatorname{uniqueCaptureCount}(C, i) = \operatorname{captureSpectrum}(C, \operatorname{captureMultiplicityOne}(C)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.catalogRoleHistogram_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.42 (Hierarchy spectrum total).**

$$\sum_{k} \operatorname{captureSpectrum}(C, k) = \operatorname{card}(\operatorname{offDiagonalPairs}(\operatorname{State}(A))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.spectrum_total` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.43 (Hierarchy zero-multiplicity bucket).**

$$\operatorname{captureSpectrum}(C, 0) = \operatorname{card}(\operatorname{escapePairs}(C, \operatorname{fullIndexSet}(C))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.spectrum_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.44 (Hierarchy multiplicity-one bucket).**

$$\operatorname{captureSpectrum}(C, \operatorname{captureMultiplicityOne}(C)) = \sum_{i} \operatorname{uniqueCaptureCount}(C, i).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.spectrum_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.45 (Hierarchy first spectrum moment).**

$$\sum_{k} k \times \operatorname{captureSpectrum}(C, k) = \sum_{i} \operatorname{card}(\operatorname{capturePairs}(C, i)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.spectrum_first_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.46 (Hierarchy second spectrum moment).**

$$\operatorname{captureSpectrumSecondFactorialMoment}(C) = \operatorname{orderedDistinctOverlapTotal}(C).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.spectrum_second_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.47 (Overlap symmetry and diagonal law).**

$$\operatorname{pairwiseCaptureOverlapPairs}(C, i, j) = \operatorname{pairwiseCaptureOverlapPairs}(C, j, i) \land \operatorname{pairwiseCaptureOverlapPairs}(C, i, i) = \operatorname{capturePairs}(C, i).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.overlap_symmetric_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

**Theorem 1.48 (Refinement determines overlap).**

$$\operatorname{KernelRefines}(C, i, j) \Rightarrow \left(\operatorname{capturePairs}(C, j) \subseteq \operatorname{capturePairs}(C, i) \land \operatorname{pairwiseCaptureOverlapPairs}(C, i, j) = \operatorname{capturePairs}(C, j)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.refinement_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.CatalogRedundant`
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
