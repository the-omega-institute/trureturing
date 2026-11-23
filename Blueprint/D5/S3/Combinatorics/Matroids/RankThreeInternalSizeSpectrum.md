# Attainable Numbers of Internal Triples

## Abstract

The exact range of sizes of internal extensions follows from a finite packing problem in each residue class.

**Definition 1.1 (The packing number on a finite label set).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeInternalSizeSpectrum.packingNumber`

*Formalization.* `D5/S3/Combinatorics/Matroids/RankThreeInternalSizeSpectrum.packingNumber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The packing number is the maximum size of a family of three-element label sets in which each pair of distinct labels occurs in at most one member. The empty family is allowed.

**Theorem 1.2 (The full interval of attainable sizes).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeInternalSizeSpectrum.exact_size_spectrum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeInternalSizeSpectrum.exact_size_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix positive row dimension and class size, the lifted pair-unique family of zero-sum triples on distinct rows covering every cross-row pair. Label each actual residue class by Fin r using the uniform residue indexing. Add unordered triples of three distinct points within rows, preserving pair uniqueness and normalized potential dimension one more than the row dimension.

The lower endpoint is the number of Latin cells across all rows. The upper endpoint adds the packing number times the number of row and residue-class pairs. Every integer between the endpoints occurs.

The unordered blocks split into the Latin cells and disjoint transported packing families. For the upper bound, each class contributes at most the packing number. For attainability, put a maximum pack in each class and choose an arbitrary subset of the union of these packing blocks. Each class remains a valid partial Steiner system, so the realization theorem preserves the required dimension.

**Definition 1.3 (Dimension-preserving internal extensions).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeInternalSizeSpectrum.IsInternalExtension`

*Formalization.* `D5/S3/Combinatorics/Matroids/RankThreeInternalSizeSpectrum.IsInternalExtension` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An internal extension is the unordered family of distinct-point triples added within rows. The combined family uses each point pair at most once and has normalized ternary potential dimension one more than the row dimension.

**Definition 1.4 (Saturated internal extensions).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeInternalSizeSpectrum.IsSaturatedInternalExtension`

*Formalization.* `D5/S3/Combinatorics/Matroids/RankThreeInternalSizeSpectrum.IsSaturatedInternalExtension` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A compatible extension is saturated if every compatible extension that contains it is equal to it.

**Theorem 1.5 (A triple from a larger extension can be added on its own).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeInternalSizeSpectrum.internal_extension_insert`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeInternalSizeSpectrum.internal_extension_insert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix the lifted cross-row family satisfying pair uniqueness. For compatible internal extensions ordered by inclusion, any triple in the larger family can be adjoined to the smaller while preserving the dimension. The two families determine the same rowwise Latin squares. An added triple enlarges one partial Steiner system by a block from the corresponding larger system.

**Theorem 1.6 (Saturation in each residue class).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeInternalSizeSpectrum.saturated_internal_extension_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeInternalSizeSpectrum.saturated_internal_extension_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same mixed-family hypotheses and any labelling preserving the actual residue, an internal extension is saturated exactly when its decomposition consists of Latin squares and inclusion-maximal partial Steiner systems in every row and residue class. Any proper compatible enlargement changes at least one class, and every local enlargement gives a compatible global enlargement.

**Theorem 1.7 (The saturated sizes with six labels in each class).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeInternalSizeSpectrum.saturated_six_size_spectrum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeInternalSizeSpectrum.saturated_six_size_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix positive row dimension d, cyclic size eighteen, and a pair-unique lifted mixed family with distinct rows in each triple and zero-sum completion of every cross-row pair. The saturated numbers of unordered internal triples are 36 times 3 to the power d, plus 2 times 3 to the power d+1, plus 2k, for k between zero and 3 to the power d+1.

The local sizes two and four follow from the classical maximal-packing results surveyed by Colbourn in sections 2.3.1 through 2.3.3 (https://ajc.maths.uq.edu.au/pdf/4/ocr-ajc-v4-p143.pdf). The Lean proof checks the six-label classification with an exhaustive finite certificate. Both sizes occur. Each residue class contributes two blocks and can independently contribute two more. The Latin squares contribute 36 blocks per row.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeInternalSizeSpectrum.IsInternalExtension`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeInternalSizeSpectrum.IsSaturatedInternalExtension`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeInternalSizeSpectrum.exact_size_spectrum`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeInternalSizeSpectrum.internal_extension_insert`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeInternalSizeSpectrum.packingNumber`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeInternalSizeSpectrum.saturated_internal_extension_iff`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeInternalSizeSpectrum.saturated_six_size_spectrum`
- Dependency: [D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition](RankThreeInternalSteinerDecomposition.md)
- Dependency: [D5/S3/Combinatorics/Matroids/RankThreeMinimumInternalAdditions](RankThreeMinimumInternalAdditions.md)
