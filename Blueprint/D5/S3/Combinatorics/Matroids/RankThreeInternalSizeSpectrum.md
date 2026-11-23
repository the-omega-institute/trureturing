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

Fix positive row dimension and class size, the lifted pair-unique family of zero-sum triples on distinct rows covering every cross-row pair, and labellings preserving the actual residue modulo three. Add unordered triples of three distinct points within rows, preserving pair uniqueness and normalized potential dimension one more than the row dimension.

The lower endpoint is the number of Latin cells across all rows. The upper endpoint adds the packing number times the number of row and residue-class pairs. Every integer between the endpoints occurs.

The unordered blocks split into the Latin cells and disjoint transported packing families. For the upper bound, each class contributes at most the packing number. For attainability, put a maximum pack in each class and choose an arbitrary subset of the union of these packing blocks. Each class remains a valid partial Steiner system, so the realization theorem preserves the required dimension.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeInternalSizeSpectrum.exact_size_spectrum`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeInternalSizeSpectrum.packingNumber`
- Dependency: [D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition](RankThreeInternalSteinerDecomposition.md)
