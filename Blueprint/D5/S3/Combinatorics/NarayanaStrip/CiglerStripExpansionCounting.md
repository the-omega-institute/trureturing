# Counting the Fixed Gap Tuples

## Abstract

The fixed colored gap tuples are counted by weak compositions of half the total number of colors.

**Definition 1.1 (Expand the half-lengths).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionCounting.doubleGapLengths`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionCounting.doubleGapLengths` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

Given a list of natural numbers and a natural remainder r, double every entry and insert a zero between consecutive doubled entries, then add r to the final doubled entry. A singleton a becomes the singleton 2a + r, and the empty list remains empty.

**Definition 1.2 (Recover the half-lengths).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionCounting.halveGaps`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionCounting.halveGaps` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

From a list of colored gaps, retain the lengths of its even-indexed gaps, numbering from zero, and divide each retained length by two with integer division. A singleton gap contributes half its length, and an empty list contributes no entries. The odd-indexed gaps are omitted.

**Theorem 1.3 (Fixed gaps and weak compositions).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionCounting.fixed_gap_bijection`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionCounting.fixed_gap_bijection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

For every nonnegative integer j and every Boolean color sequence of length L, the fixed gap tuples with 2j + 1 gaps and that concatenated color sequence are in bijection with the weak compositions of floor(L/2) into j + 1 parts. The forward map takes the half-lengths of the even-indexed gaps. The inverse doubles those parts, inserts zero lengths between them, adds the remainder of L modulo two to the last length, and splits the color sequence at those lengths. For any finite set consisting exactly of all tuples with 2j + 1 gaps and that concatenation, the sum of (-1)^q, where q is the total length of the odd-indexed gaps, is binom(floor(L/2) + j, j).

## References

- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionCounting.doubleGapLengths`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionCounting.fixed_gap_bijection`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionCounting.halveGaps`
- Dependency: [D5/S3/Combinatorics/ArrowWilfTwelveSurject](../ArrowWilfTwelveSurject.md)
- Dependency: [D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionCancellation](CiglerStripExpansionCancellation.md)
