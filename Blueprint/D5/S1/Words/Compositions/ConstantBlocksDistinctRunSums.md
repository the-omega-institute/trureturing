# Constant Blocks and Distinct Run Sums

## Abstract

Distinct-sum constant blocks exist exactly when an ordering has distinct maximal run sums.

OEIS A382427 compares two existence predicates on positive integer partitions. A block is encoded as (value, multiplicity), with both entries positive. Blocks may share a value, but their sums must all differ. A381717 states the pointwise equivalence for the complementary class.

**Definition 1.1 (Constant blocks with distinct sums).**

$$\forall m: \operatorname{Multiset}\left(\mathbb{N}\right), \operatorname{HasConstantBlocks}\left(m\right) \iff (\exists s: \operatorname{Finset}\left((\mathbb{N}\times\mathbb{N})\right), (\forall b \in s, 0<\operatorname{fst}\left(b\right) \land 0<\operatorname{snd}\left(b\right)) \land \operatorname{InjOn}\left((b \mapsto \operatorname{fst}\left(b\right) \cdot \operatorname{snd}\left(b\right)), s\right) \land \operatorname{sum}\left(s, (b \mapsto \operatorname{replicate}\left(\operatorname{snd}\left(b\right), \operatorname{fst}\left(b\right)\right))\right) = m)$$

*Formalization.* `D5/S1/Words/Compositions/ConstantBlocksDistinctRunSums.HasConstantBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2025). *OEIS A382427*. URL: <https://oeis.org/A382427>.

*Commentary.*

The finite set records every block. A repeated identical block would repeat its sum, so no valid decomposition is lost by using a set. Replicate(c,v) is the multiset containing c copies of v; the multiset sum preserves every part and its multiplicity. InjOn requires distinct sums across all values.

**Definition 1.2 (Maximal constant runs).**

$$\forall l: \operatorname{List}\left(\mathbb{N}\right), \operatorname{runSums}\left(l\right) = \operatorname{map}\left(sum, \operatorname{splitBy}\left((a,b \mapsto \operatorname{beq}\left(a, b\right)), l\right)\right)$$

*Formalization.* `D5/S1/Words/Compositions/ConstantBlocksDistinctRunSums.runSums` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2025). *OEIS A382427*. URL: <https://oeis.org/A382427>.

*Commentary.*

Mathlib List.splitBy with Boolean equality splits at each change of value. The resulting runs are maximal; mapping List.sum takes their sums. The empty list has no runs and no sums.

**Definition 1.3 (An ordering with distinct run sums).**

$$\forall m: \operatorname{Multiset}\left(\mathbb{N}\right), \operatorname{HasDistinctRunSums}\left(m\right) \iff (\exists l: \operatorname{List}\left(\mathbb{N}\right), (l: \operatorname{Multiset}\left(\mathbb{N}\right)) = m \land \operatorname{Nodup}\left(\operatorname{runSums}\left(l\right)\right))$$

*Formalization.* `D5/S1/Words/Compositions/ConstantBlocksDistinctRunSums.HasDistinctRunSums` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2025). *OEIS A382427*. URL: <https://oeis.org/A382427>.

*Commentary.*

Equality of the underlying multiset expresses that the list is a permutation of the parts. Nodup tests all run sums together. No ordering of the parts is fixed in advance, and only existence is counted.

**Theorem 1.4 (Pointwise equivalence).**

$$\forall n: \mathbb{N}, \forall p: \operatorname{Partition}\left(n\right), \operatorname{HasConstantBlocks}\left(\operatorname{parts}\left(p\right)\right) \iff \operatorname{HasDistinctRunSums}\left(\operatorname{parts}\left(p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/ConstantBlocksDistinctRunSums.constantBlocks_iff_distinctRunSums` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2025). *OEIS A382427*. URL: <https://oeis.org/A382427>.

*Commentary.*

Choose a valid decomposition with the fewest blocks. If k blocks share a value and there are o other blocks, k > o+1 supplies k-1 different candidate sums by adding the largest same-value sum to each remaining one. Each candidate exceeds every old same-value sum, so one avoids all o other sums. Merging that pair contradicts minimality. Thus every color count obeys 2k <= total+1. A greedy induction, retaining a forbidden first color, orders the blocks with adjacent values different. Mathlib splitBy_flatten then certifies that these blocks are exactly the maximal runs. Conversely, the maximal runs themselves provide the constant-block decomposition.

**Theorem 1.5 (The A382427 counting identity).**

$$\forall n: \mathbb{N}, \operatorname{card}\left(\operatorname{filter}\left((p \mapsto \operatorname{HasConstantBlocks}\left(\operatorname{parts}\left(p\right)\right)), (\operatorname{univ}\left(\right): \operatorname{Finset}\left(\operatorname{Partition}\left(n\right)\right))\right)\right) = \operatorname{card}\left(\operatorname{filter}\left((p \mapsto \operatorname{HasDistinctRunSums}\left(\operatorname{parts}\left(p\right)\right)), (\operatorname{univ}\left(\right): \operatorname{Finset}\left(\operatorname{Partition}\left(n\right)\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/ConstantBlocksDistinctRunSums.card_constantBlocks_eq_distinctRunSums` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a382427-constant-blocks-distinct-run-sums` (proved) by `D5/S1/Words/Compositions/ConstantBlocksDistinctRunSums.card_constantBlocks_eq_distinctRunSums`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a382427-constant-blocks-distinct-run-sums","declaration_gid":"D5/S1/Words/Compositions/ConstantBlocksDistinctRunSums.card_constantBlocks_eq_distinctRunSums","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2025). *OEIS A382427*. URL: <https://oeis.org/A382427>.

*Commentary.*

The pointwise equivalence identifies two filters of the same finite type Nat.Partition(n), and hence their cardinalities. This holds for every n, including n=0, whose unique partition is empty and satisfies both predicates.

## References

- Truth anchor: `D5/S1/Words/Compositions/ConstantBlocksDistinctRunSums.HasConstantBlocks`
- Truth anchor: `D5/S1/Words/Compositions/ConstantBlocksDistinctRunSums.HasDistinctRunSums`
- Truth anchor: `D5/S1/Words/Compositions/ConstantBlocksDistinctRunSums.card_constantBlocks_eq_distinctRunSums`
- Truth anchor: `D5/S1/Words/Compositions/ConstantBlocksDistinctRunSums.constantBlocks_iff_distinctRunSums`
- Truth anchor: `D5/S1/Words/Compositions/ConstantBlocksDistinctRunSums.runSums`
