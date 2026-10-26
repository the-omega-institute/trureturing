# Literal contiguous blocks

## Abstract

Exact original finite permutation counts and overlap-sensitive forbidden-family avoidance.

Let A be an arbitrary finite set of original labels. The space orders A is the existing actual List permutation inventory, with cardinality |A|!, from DisjointBlockContraction. A nonempty prescribed S subset A is forbidden when precisely its elements, in any internal order, occupy one literal interval. Full S=A is allowed in the counting theorem. No labels are removed, identified or sampled under an assumed probability law.

**Definition 1.1 (A literal interval).**

Lean statement: `D5/S3/Combinatorics/Permutation/ForbiddenContiguousBlocks.Block`

*Formalization.* `D5/S3/Combinatorics/Permutation/ForbiddenContiguousBlocks.Block` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Block S w means w=p++u++v for actual lists p,u,v with u a permutation of S.toList.

**Theorem 1.2 (The exact compression count).**

Lean statement: `D5/S3/Combinatorics/Permutation/ForbiddenContiguousBlocks.block_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/ForbiddenContiguousBlocks.block_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonempty S subset A, the number of original permutations in which S is a block is |S|!*(|A|-|S|+1)!. Adjoin a fresh separator none, root the circle at that separator, and prove both directions of the correspondence between linear blocks and proper circular arcs. The existing anchorEquiv and actual twoBlockEquiv then give inverse compression and expansion maps. The separator is only an auxiliary counting marker; it adds no original label or group relation.

**Theorem 1.3 (Finite-family avoidance including equality).**

Lean statement: `D5/S3/Combinatorics/Permutation/ForbiddenContiguousBlocks.exists_avoiding`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/ForbiddenContiguousBlocks.exists_avoiding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary finite indexed family of nonempty subsets H(i) of A, sum their exact block counts. A strict bound below |A|! gives an avoiding original order. A weak bound suffices if one actual original order has block incidences at two different indices. Double counting actual (word,index) pairs shows that if every word had a bad incidence, this overlap word would force the total strictly above |A|!. Repeated indexed sets are permitted; incidences are counted with their index multiplicity. No independence assumption is used.

**Theorem 1.4 (A genuine overlap word).**

Lean statement: `D5/S3/Combinatorics/Permutation/ForbiddenContiguousBlocks.two_intersecting_blocks`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/ForbiddenContiguousBlocks.two_intersecting_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If S and T are original subsets of A with intersection exactly {p}, concatenate an order of S without p, then p, then an order of T without p, then all remaining original elements. This is one actual permutation with both S and T as intervals. It supplies the equality-boundary overlap used by ProjectivePlaneGoodOrdering; it does not assert that this word avoids any forbidden set.

The substantive new inference is faithful separator transport and the resulting exact linear block count, reused on the live avoidance proof path. The intersecting-set construction is a consumed auxiliary of the plane application. Existing circular contraction/counting and pinned Mathlib finite sums, factorials and double counting are reused. Bounded library searches found no dominating linear-family contract in the inspected sources; this is not an exhaustive absence or external novelty claim. Utility none: the statements and proofs are symbolic over arbitrary finite sets, not a fixed finite census, checker or certified instance.

Four-slot information-escape registration is unfinished for these public targets and is disclosed under the linked issue https://github.com/the-omega-institute/trureturing/issues/22019. Lean/kernel verification and this incomplete audit are separate; no declared_validated claim is made.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/ForbiddenContiguousBlocks.Block`
- Truth anchor: `D5/S3/Combinatorics/Permutation/ForbiddenContiguousBlocks.block_card`
- Truth anchor: `D5/S3/Combinatorics/Permutation/ForbiddenContiguousBlocks.exists_avoiding`
- Truth anchor: `D5/S3/Combinatorics/Permutation/ForbiddenContiguousBlocks.two_intersecting_blocks`
- Dependency: [D5/S3/Combinatorics/CircularWords/CircleBlockEquivalence](../CircularWords/CircleBlockEquivalence.md)
