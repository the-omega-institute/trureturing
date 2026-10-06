# Transfer Matrices for Signed Strip Paths

## Abstract

Weighted words give transfer matrix powers, and pairing Dyck steps relates signed strip sums to a path with endpoint loops.

**Definition 1.1 (The contribution of a labeled word).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer.wordContribution`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer.wordContribution` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

Given a set of states, a label alphabet, a transition function and an integer weight for each state and label, the contribution of a word from a starting state to a target is the product of its successive transition weights if its final state is the target, and zero otherwise. The empty word contributes one when the starting state is the target and zero otherwise.

**Theorem 1.2 (Weighted words and matrix powers).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer.weighted_walks_eq_pow`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer.weighted_walks_eq_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

For finite state and label sets, let T(s, t) be the sum of the weights of labels that send s to t. For every natural number r and every pair of states s and t, the sum of word contributions over all label sequences of length r starting at s and ending at t equals T^r(s, t). Transition weights are arbitrary integers, and distinct labels with the same destination contribute separately to the matrix entry.

**Definition 1.3 (Transitions of paired steps).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer.pairedTransition`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer.pairedTransition` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

The states are heights zero through b minus one. A pair of up-steps raises the height by one with weight one if the new height is below b; otherwise it stays at its starting height with weight zero. A pair of down-steps lowers a positive height by one with weight minus one; at height zero it stays there with weight zero. Either mixed pair stays at height h with weight (-1)^h.

**Definition 1.4 (The paired transition matrix).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer.pairedAdj`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer.pairedAdj` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

For a natural number b, pairedAdj is the integer matrix on the b heights whose entry from s to t sums the weights of all four ordered pairs of Boolean steps having destination t under pairedTransition. The two mixed pairs are distinct contributions, so their total diagonal weight at height h is 2(-1)^h.

**Theorem 1.5 (The signed strip sum as a paired moment).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer.paired_strip_eq_pow`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer.paired_strip_eq_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

For every positive integer b and nonnegative integer r, the signed Dyck path sum of semilength r plus one in the strip of height 2b equals the entry at (0, 0) of pairedAdj(b)^r. Removing the enclosing up-step and down-step and pairing the remaining steps gives a two-colored Motzkin excursion with r steps at heights zero through b minus one, preserving its signed weight.

**Definition 1.6 (A path with loops at both ends).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer.foldedAdj`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer.foldedAdj` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

For a natural number v, foldedAdj is the integer adjacency matrix on vertices zero through v minus one. Two consecutive vertices have entry one. A diagonal entry is one at vertex zero and at vertex v minus one, and all other entries are zero. When v is one there is a single loop of weight one, and when v is zero the matrix has no entries.

**Theorem 1.7 (The signed strip sum as a looped-path moment).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer.strip_eq_folded`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer.strip_eq_folded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

For every positive odd integer b and nonnegative integer r, the signed Dyck path sum of semilength r plus one in the strip of height 2b equals foldedAdj(b + 1)^{r+1}(0, 0). Rectangular matrices factor the paired transition matrix in one order and the looped-path adjacency matrix in the reverse order. Alternating signs cancel the interior diagonal entries, while odd b gives a loop of weight one at each endpoint.

## References

- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer.foldedAdj`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer.pairedAdj`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer.pairedTransition`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer.paired_strip_eq_pow`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer.strip_eq_folded`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer.weighted_walks_eq_pow`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer.wordContribution`
- Dependency: [D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkDefs](CiglerCycleWalkDefs.md)
- Dependency: [D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs](CiglerStripExpansionDefs.md)
- Dependency: [D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionPairing](CiglerStripExpansionPairing.md)
