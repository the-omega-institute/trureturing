# Universal soundness of the complete finite recursion

## Abstract

A complete include-or-omit checker for weighted independent sets.

**Theorem 1.1 (All compatible subsets).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/WeightedIndependentBound.sound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/WeightedIndependentBound.sound` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

For every finite candidate list over any decidable type, every natural weight function and every Boolean compatibility relation, the include-or-omit bound dominates the weight of every pairwise compatible finite subset. The fuel must be at least the full candidate length. In the include branch, erase the selected candidate and restrict every other vertex by its compatibility; in the omit branch retain the tail. Induction on fuel proves both branches, without an assumed maximum, a sample, or a caller-supplied completeness premise. The first actual consumer is the received O2 weighted inequality on all63 nonzero six-bit vectors, with its complete computed bound19. This independent formal checker is a proof representation for the supplied scientific result; it does not replace attribution of the manuscript's Gram/radical proof.

## References

- Truth anchor: `D5/S3/Combinatorics/Orthogonality/WeightedIndependentBound.sound`
