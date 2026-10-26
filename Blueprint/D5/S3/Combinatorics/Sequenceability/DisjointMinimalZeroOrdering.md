# Disjoint minimal zero supports admit a Good ordering

## Abstract

Constructing original-occurrence Good orders from disjoint zero-support blocks.

**Theorem 1.1 (An unconditional block-union constructor).**

Lean statement: `D5/S3/Combinatorics/Sequenceability/DisjointMinimalZeroOrdering.good_order_of_disjoint_zero_blocks`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Sequenceability/DisjointMinimalZeroOrdering.good_order_of_disjoint_zero_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be a finite set of original occurrence indices, with labels f into any additive commutative group. Let P be pairwise disjoint subsets of X, each of cardinality at least two. Assume every nonempty coefficient-one zero support C contained in X is a union of members of P. The theorem constructs a list w permuting X.toList for which the original Good predicate holds on w.map f: every nonempty proper contiguous interval has nonzero sum. P need not cover X, and neither zero total nor nonzero total is required. No Good compressed order, legal edge, ordering induction hypothesis, torsion restriction or bound on X is assumed.

Choose distinct original indices a(B), b(B) in each block and enumerate the blocks. Form the literal word a(1),...,a(k), followed by every remaining original index once, followed by b(1),...,b(k) in the same block order. The middle includes all indices outside the blocks and all unchosen indices inside blocks. Pairwise block disjointness proves the occurrence inventory is a permutation, without identifying indices by their label values. A zero interval is a union of complete blocks, so it contains a(B) exactly when it contains b(B). If it is nonempty, it contains one such pair. It therefore reaches across the middle. For every earlier block its second chosen occurrence lies inside the interval, and for every later block its first chosen occurrence lies inside. Closure under pairs forces the first occurrence a(1) and the final occurrence b(k) into the interval. Hence the interval is the entire word. With no blocks, the assumed zero-support description excludes every nonempty zero interval directly.

**Theorem 1.2 (Disjoint inclusion-minimal zero supports suffice).**

Lean statement: `D5/S3/Combinatorics/Sequenceability/DisjointMinimalZeroOrdering.good_order_of_disjoint_minimal_zero_supports`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Sequenceability/DisjointMinimalZeroOrdering.good_order_of_disjoint_minimal_zero_supports` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite original index set X with nonzero labels into any additive commutative group, assume distinct inclusion-minimal nonempty zero supports contained in X are pairwise disjoint. The theorem constructs an actual permutation w of X with Good (w.map f). In particular it applies to injective nonzero labels; the interval argument also works without injectivity because it tracks original occurrence identities.

The proof supplies the block-union premise rather than assuming it. Inside a nonempty zero support C choose an inclusion-minimal nonempty zero support B using well-founded finite-set inclusion. The difference C minus B is smaller and has sum zero by subtraction. Finite deletion induction decomposes C into minimal zero supports, all still contained in X. Each minimal support has at least two indices: a singleton zero support would have a zero label. The finite family of all minimal supports is extracted from the powerset of X and passed to the preceding constructor. Empty X, absence of zero supports, a single minimal block, arbitrary total sum and every torsion characteristic remain in scope.

This is a sufficient structural class for the original Good convention, not a solution of unrestricted Good, the original connector, or AM. Contrapositively, a primitive-free full interval blocker must have intersecting distinct minimal Boolean kernel rows: otherwise this constructor supplies a Good word. This consequence is explanatory and adds no retained wrapper theorem. Existing conditional adaptive/compression results are unchanged. Repository and pinned-mathlib search establish reuse boundaries, not literature novelty. The faithful dependent-family Reg attempt compiled, but current public four-slot binding remains unfinished: the inspector rejects four ambient universe parameters in the registration packaging with contract.discovery:rigid_universes. The exact full-source audit gap and compiled evidence are recorded in https://github.com/the-omega-institute/trureturing/issues/21987. No declared_validated registration is claimed; this limitation is separate from Lean/kernel acceptance.

## References

- Truth anchor: `D5/S3/Combinatorics/Sequenceability/DisjointMinimalZeroOrdering.good_order_of_disjoint_minimal_zero_supports`
- Truth anchor: `D5/S3/Combinatorics/Sequenceability/DisjointMinimalZeroOrdering.good_order_of_disjoint_zero_blocks`
- Dependency: [D5/S3/Combinatorics/Sequenceability/PairedZeroSubsetSpectrum](PairedZeroSubsetSpectrum.md)
