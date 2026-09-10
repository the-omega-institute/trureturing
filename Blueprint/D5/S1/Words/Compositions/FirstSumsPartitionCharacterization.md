# First Sums of Decreasing Partitions

## Abstract

A decreasing partition is not a first-sums list exactly when it has a part below four.

The source is Gus Wiseman's conjecture in OEIS A391620, dated December 30, 2025. Partition parts are listed in weakly decreasing order, and equality with the first-sums list preserves that order. For nonempty lists, having a part below four is equivalent to having least part below four.

List(N) denotes lists of natural numbers. Pairwise applies its relation to every earlier and later entry. All subtraction is natural subtraction. The list characterization does not require positivity; Mathlib Partition(n) supplies positive parts summing to n.

**Definition 1.1 (Adjacent sums).**

$$\forall x: \operatorname{List}(\mathbb{N}), \operatorname{firstSums}(x) = \operatorname{zipWith}(((a, b: \mathbb{N}) \mapsto a + b), x, \operatorname{tail}(x))$$

*Formalization.* `D5/S1/Words/Compositions/FirstSumsPartitionCharacterization.firstSums` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

zipWith adds corresponding entries of a list and its tail. Empty lists and singleton lists both have empty first-sums lists.

**Definition 1.2 (Realizability with parts at least two).**

$$\forall q: \operatorname{List}(\mathbb{N}), \operatorname{IsFirstSums}(q) \iff (\exists x: \operatorname{List}(\mathbb{N}), (\forall y: \mathbb{N}, y \in x \implies 2 \le y) \land \operatorname{firstSums}(x) = q)$$

*Formalization.* `D5/S1/Words/Compositions/FirstSumsPartitionCharacterization.IsFirstSums` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The witness is a list of natural numbers, every entry at least two, whose adjacent sums equal q. The empty target is allowed.

**Lemma 1.3 (Length of the adjacent-sums list).**

$$\forall x: \operatorname{List}(\mathbb{N}), \operatorname{length}(\operatorname{firstSums}(x)) = \operatorname{length}(x) - 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/FirstSumsPartitionCharacterization.firstSums_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib's zipWith length identity reduces the length to the minimum of the lengths of x and its tail, hence length(x)-1.

**Lemma 1.4 (The necessary lower bound).**

$$\forall q: \operatorname{List}(\mathbb{N}), \operatorname{IsFirstSums}(q) \implies (\forall y: \mathbb{N}, y \in q \implies 4 \le y)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/FirstSumsPartitionCharacterization.min_ge_four_of_isFirstSums` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Select a realizing list. Every adjacent sum is at least 2+2, so every entry of its first-sums list is at least four.

**Theorem 1.5 (Backward reconstruction).**

$$\forall q: \operatorname{List}(\mathbb{N}), q \neq [] \implies \operatorname{Pairwise}(((a, b: \mathbb{N}) \mapsto a \ge b), q) \implies (\forall y: \mathbb{N}, y \in q \implies 4 \le y) \implies \operatorname{IsFirstSums}(q)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/FirstSumsPartitionCharacterization.isFirstSums_of_sorted_min_ge_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a singleton [a], use [a-2,2]. Given a realization of the suffix beginning at b whose first entry u satisfies 2 <= u <= b-2, prepend a-u. Since b <= a, this new entry is at least two and at most a-2, and its sum with u is a. Induction constructs a realization for every nonempty decreasing list with parts at least four.

**Theorem 1.6 (Wiseman's characterization).**

$$\forall q: \operatorname{List}(\mathbb{N}), q \neq [] \implies \operatorname{Pairwise}(((a, b: \mathbb{N}) \mapsto a \ge b), q) \implies (\neg \operatorname{IsFirstSums}(q) \iff (\exists y: \mathbb{N}, y \in q \land y < 4))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/FirstSumsPartitionCharacterization.wiseman_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a391620-first-sums-partition-characterization` (proved) by `D5/S1/Words/Compositions/FirstSumsPartitionCharacterization.wiseman_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a391620-first-sums-partition-characterization","declaration_gid":"D5/S1/Words/Compositions/FirstSumsPartitionCharacterization.wiseman_conjecture","resolution_kind":"proved"} -->

*Citation.* Gus Wiseman (2025). *OEIS A391620, partitions that are not first sums of a composition with all parts > 1*. URL: <https://oeis.org/A391620>.

*Commentary.*

If there is no part below four, backward reconstruction supplies a realization. Conversely, a part below four contradicts the necessary lower bound. This proves the conjecture for the ordered-part reading.

**Theorem 1.7 (Equality of partition counts).**

$$\forall n: \mathbb{N}, \operatorname{card}(\operatorname{filter}(((p: \operatorname{Partition}(n)) \mapsto \neg \operatorname{IsFirstSums}(\operatorname{sort}(\operatorname{parts}(p), ((a, b: \mathbb{N}) \mapsto a \ge b)))), (\operatorname{univ}(): \operatorname{Finset}(\operatorname{Partition}(n))))) = \operatorname{card}(\operatorname{filter}(((p: \operatorname{Partition}(n)) \mapsto (\exists y: \mathbb{N}, y \in \operatorname{parts}(p) \land y < 4)), (\operatorname{univ}(): \operatorname{Finset}(\operatorname{Partition}(n)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/FirstSumsPartitionCharacterization.card_not_firstSums_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sort each partition's multiset of parts in decreasing order. Sorting preserves membership, so the characterization makes the two filters equal and hence their cardinalities equal. The empty list is realized by [2], so the equality also holds at n=0.

## References

- Truth anchor: `D5/S1/Words/Compositions/FirstSumsPartitionCharacterization.IsFirstSums`
- Truth anchor: `D5/S1/Words/Compositions/FirstSumsPartitionCharacterization.card_not_firstSums_eq`
- Truth anchor: `D5/S1/Words/Compositions/FirstSumsPartitionCharacterization.firstSums`
- Truth anchor: `D5/S1/Words/Compositions/FirstSumsPartitionCharacterization.firstSums_length`
- Truth anchor: `D5/S1/Words/Compositions/FirstSumsPartitionCharacterization.isFirstSums_of_sorted_min_ge_four`
- Truth anchor: `D5/S1/Words/Compositions/FirstSumsPartitionCharacterization.min_ge_four_of_isFirstSums`
- Truth anchor: `D5/S1/Words/Compositions/FirstSumsPartitionCharacterization.wiseman_conjecture`
