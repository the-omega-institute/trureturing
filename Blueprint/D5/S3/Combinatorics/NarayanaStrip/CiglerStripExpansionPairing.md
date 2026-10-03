# Pairing Dyck Steps into Motzkin Steps

## Abstract

Pairing the interior steps of an even-strip Dyck path gives a two-colored Motzkin path with the same weight.

**Definition 1.1 (Expand a sequence of pairs).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionPairing.expandBlocks`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionPairing.expandBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

Expand each ordered pair of Boolean steps into its first step followed by its second step, preserving the order of all pairs. The empty sequence of pairs expands to the empty sequence of steps.

**Definition 1.2 (Group consecutive steps into pairs).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionPairing.pairBlocks`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionPairing.pairBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

Group a Boolean step sequence into consecutive ordered pairs, starting at its first step. If the sequence has odd length, its last step is discarded. A sequence of length zero or one produces no pairs.

**Definition 1.3 (Enclose the expanded pairs).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionPairing.expandPath`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionPairing.expandPath` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

Expand the sequence of pairs, prepend one up-step and append one down-step. A sequence of n pairs therefore gives a path of length 2(n + 1). An up-step is represented by true and a down-step by false.

**Definition 1.4 (The coarse prefix height).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionPairing.coarseHeight`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionPairing.coarseHeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

The coarse height after k pairs is the sum of the first k coarse increments. A pair of two up-steps contributes one, a pair of two down-steps contributes minus one, and either mixed pair contributes zero. Taking more pairs than are present uses the entire sequence.

**Definition 1.5 (Motzkin paths in a strip).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionPairing.IsMotzkinStrip`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionPairing.IsMotzkinStrip` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

For a natural number b, a sequence of pairs represents a two-colored Motzkin path in the strip of height b when every coarse prefix height lies between zero and b, inclusive, and its final coarse height is zero. The mixed pairs up-down and down-up are the two colors of horizontal step.

**Definition 1.6 (Ordinary and signed Motzkin weights).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionPairing.motzkinWeight`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionPairing.motzkinWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

Starting at a natural height a, multiply the successive coarse step weights while updating the height. An up-step has weight one and increases the height by one. A down-step decreases the height by one, with subtraction truncated at zero, and has weight t in the ordinary case and minus t in the signed case. An up-down horizontal pair has weight t and a down-up pair has weight one. In the signed case each horizontal weight is additionally multiplied by (-1)^a at its current height. The empty sequence has weight one.

**Theorem 1.7 (The even-strip pairing bijection).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionPairing.pairing_bijection`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionPairing.pairing_bijection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

For every positive integer m and nonnegative integer n, Dyck paths of length 2(n + 1) in the strip of height 2m are in bijection with two-colored Motzkin paths of length n in the strip of height m minus one. Expansion of the image of any Dyck path recovers that path, and the inverse map on every Motzkin path is expansion enclosed by an initial up-step and a final down-step.

**Theorem 1.8 (Preservation of both weights).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionPairing.pairing_weights`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionPairing.pairing_weights` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

For every natural strip height b and every two-colored Motzkin path in that strip, its enclosed expansion has Narayana weight equal to its ordinary Motzkin weight starting at height zero. Its signed Narayana weight equals its signed Motzkin weight starting at height zero.

## References

- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionPairing.IsMotzkinStrip`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionPairing.coarseHeight`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionPairing.expandBlocks`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionPairing.expandPath`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionPairing.motzkinWeight`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionPairing.pairBlocks`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionPairing.pairing_bijection`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionPairing.pairing_weights`
- Dependency: [D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs](CiglerStripExpansionDefs.md)
