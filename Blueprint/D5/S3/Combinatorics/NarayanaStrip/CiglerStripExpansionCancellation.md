# Sign-Reversing Cancellation of Colored Gaps

## Abstract

A color-preserving involution cancels the signed weights of all gap tuples except those with paired colors in the even-indexed gaps.

**Definition 1.1 (The first-defect gap transformation).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionCancellation.gapInvolution`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionCancellation.gapInvolution` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

Inspect successive pairs consisting of an even-indexed gap and the following odd-indexed gap, with indices starting at zero. If the even gap has even length and the odd gap is empty, leave both in place and continue. If the even gap has even length and the odd gap is nonempty, move the first color of the odd gap to the end of the even gap. If the even gap has odd length, move its last color to the start of the odd gap. Stop after the first move. Lists with fewer than two gaps remain unchanged.

**Definition 1.2 (The fixed gap condition).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionCancellation.FixedGaps`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionCancellation.FixedGaps` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

A colored gap tuple is fixed when, for every consecutive pair of gaps starting at an even index, the even-indexed gap has even length and the following odd-indexed gap is empty. Indices start at zero. A final unpaired gap is unrestricted, and a list with at most one gap satisfies the condition.

**Theorem 1.3 (Color-preserving sign reversal).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionCancellation.colored_gap_involution`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionCancellation.colored_gap_involution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

For every colored gap tuple, the gap transformation preserves both the number of gaps and their concatenated color sequence, and applying it twice returns the original tuple. Its fixed points are exactly the tuples satisfying the fixed gap condition, which have zero odd-gap charge. Every non-fixed tuple has the negative of the sign of its image, with sign (-1)^q for odd-gap charge q. There also exists an involution on Boolean pair sequences preserving their length, extracted skeleton and concatenated gap colors, whose fixed points have exactly the fixed gap condition. It preserves the Motzkin strip condition for every natural bound, and negates the signed Motzkin weight starting at height zero of every non-fixed path in that strip.

## References

- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionCancellation.FixedGaps`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionCancellation.colored_gap_involution`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionCancellation.gapInvolution`
- Dependency: [D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionSkeleton](CiglerStripExpansionSkeleton.md)
