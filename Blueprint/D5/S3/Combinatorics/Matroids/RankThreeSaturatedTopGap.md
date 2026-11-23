# The Gap Below the Largest Saturated Extension

## Abstract

The top two saturated extension sizes are controlled by the uncovered label pairs in each class.

**Theorem 1.1 (The two largest saturated extension sizes).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeSaturatedTopGap.saturated_top_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeSaturatedTopGap.saturated_top_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a positive row dimension d and at least seven labels per residue class. The lifted mixed family has three distinct rows in each triple, zero-sum completion for every cross-row pair, and pair uniqueness. Assume the labels admit a complete Steiner triple system.

Let N be the number of rowwise Latin cells, 3 to the power d times r squared, plus the number of actual residue classes, 3 to the power d+1, times r(r−1)/6. There is a saturated extension with N internal triples and one with N−2. Every saturated extension has at most N internal triples, and N−1 cannot occur.

Choose three labels that are not a block of the complete system. Remove the three blocks covering their pairs and insert the selected triple. Pair uniqueness makes the three former completion points distinct. The uncovered pairs are exactly the six alternating edges through the selected labels and the completion points. This leave has no triangle, so the resulting packing is inclusion maximal.

Each complete block covers three pairs. Removing one block from the maximum count would leave three uncovered pairs in a class of odd order. Every vertex in this leave has even degree because a used block consumes two partners at each incident vertex. Three uncovered edges with even degrees form a triangle, which could be added as a block. Thus every nonzero class deficit is at least two.

To attain the top size, use a complete system in every class. To attain the next size, use the six-cycle leave in one class and complete systems in the others. The local packing spectrum is classical. See Colbourn, sections 2.3.1 through 2.3.3 (https://ajc.maths.uq.edu.au/pdf/4/ocr-ajc-v4-p143.pdf).

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeSaturatedTopGap.saturated_top_gap`
- Dependency: [D5/S3/Combinatorics/Matroids/RankThreeInternalSizeSpectrum](RankThreeInternalSizeSpectrum.md)
