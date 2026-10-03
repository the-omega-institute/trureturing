# Dyck Skeletons and Colored Gaps

## Abstract

Deleting horizontal steps separates a two-colored Motzkin path into a Dyck skeleton and its ordered colored gaps.

**Definition 1.1 (Extract the skeleton and its gaps).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionSkeleton.extractData`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionSkeleton.extractData` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

From a sequence of Boolean pairs, retain each equal pair as a skeleton step with that Boolean value. Record each mixed pair as a horizontal color given by its first Boolean value in the gap at its location. There is one gap before the first skeleton step, one between each two consecutive skeleton steps, and one after the last. The empty sequence has an empty skeleton and a single empty gap.

**Definition 1.2 (Insert the colored gaps).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionSkeleton.insertData`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionSkeleton.insertData` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

Given a Boolean skeleton and a list of colored gaps, replace each color c in the first gap by the mixed pair (c, not c). If the skeleton is nonempty, append the equal pair for its first step and continue with the remaining skeleton and gaps. An empty gap list produces an empty sequence. When the skeleton is empty, only the first gap is used.

**Definition 1.3 (Alternating gap charge).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionSkeleton.gapCharge`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionSkeleton.gapCharge` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

The charge of a list of colored gaps is the total length of alternating gaps. A Boolean phase indicates whether the first gap has an even index: when the phase is true it contributes zero, and when the phase is false it contributes its length. The phase changes at each following gap. Starting with phase true gives the total number of colors in the gaps with odd indices, numbering gaps from zero.

**Theorem 1.4 (The skeleton decomposition bijection).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionSkeleton.skeleton_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionSkeleton.skeleton_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

Every finite sequence of Boolean pairs corresponds bijectively to a Boolean skeleton together with a list of colored gaps whose length is one more than the skeleton length. The forward map extracts the skeleton and gaps, and the inverse inserts them. The number of pairs equals the skeleton length plus the total number of colors. For every natural strip height b, the original sequence is a Motzkin path in the strip of height b exactly when its skeleton is a Dyck path in that strip.

**Theorem 1.5 (Weights determined by the skeleton and gaps).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionSkeleton.skeleton_weights`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionSkeleton.skeleton_weights` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

For every two-colored Motzkin path in a strip of natural height b, let d be the number of down-steps in its extracted skeleton, u the number of true colors in all its gaps, and q the total length of its odd-indexed gaps. Its ordinary weight starting at height zero is t^(d + u). Its signed weight starting at height zero is (-1)^(d + q) times t^(d + u). These are equalities of integer polynomials.

## References

- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionSkeleton.extractData`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionSkeleton.gapCharge`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionSkeleton.insertData`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionSkeleton.skeleton_decomposition`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionSkeleton.skeleton_weights`
- Dependency: [D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionPairing](CiglerStripExpansionPairing.md)
