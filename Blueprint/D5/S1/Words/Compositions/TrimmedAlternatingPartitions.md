# Trimmed Alternating Sums of Partitions

## Abstract

Distinct trimmed alternating sums characterize strict partition tails and count strict partitions of n+1.

Ordinary partitions are listed in weakly decreasing order. Their trimmed alternating sums exclude the initial zero and use integer subtraction. The corrected OEIS A392698 count has a shift by one; distincts denotes Mathlib's Nat.Partition.distincts. The unshifted source sentence is not the theorem proved here.

**Definition 1.1 (Integer recurrence).**

$$\forall z: \mathbb{Z}, \operatorname{sumsFrom}\left(z, \operatorname{nil}\left(\right)\right) = \operatorname{nil}\left(\right) \land (\forall a: \mathbb{N}, \forall q: \operatorname{List}\left(\mathbb{N}\right), \operatorname{sumsFrom}\left(z, \operatorname{cons}\left(a, q\right)\right) = \operatorname{cons}\left(a-z, \operatorname{sumsFrom}\left(a-z, q\right)\right))$$

*Formalization.* `D5/S1/Words/Compositions/TrimmedAlternatingPartitions.sumsFrom` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2026). *OEIS A392698*. URL: <https://oeis.org/A392698>.

*Commentary.*

The initial accumulator z is excluded. A natural part a gives the next integer value a-z; recursion continues from that value. In particular, negative values are retained, rather than truncated by natural subtraction.

**Definition 1.2 (Trimmed sums).**

$$\forall q: \operatorname{List}\left(\mathbb{N}\right), \operatorname{trimmedSums}\left(q\right) = \operatorname{sumsFrom}\left(0, q\right)$$

*Formalization.* `D5/S1/Words/Compositions/TrimmedAlternatingPartitions.trimmedSums` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2026). *OEIS A392698*. URL: <https://oeis.org/A392698>.

*Commentary.*

Start the recurrence at zero. The output for the empty list is empty; the output for [1,1] is [1,0], whose entries are distinct.

**Theorem 1.3 (The strict-tail criterion).**

$$\forall q: \operatorname{List}\left(\mathbb{N}\right), (\operatorname{Pairwise}\left((a, b \mapsto a \ge b), q\right) \land (\forall a: \mathbb{N}, a \in q \implies 0 < a)) \implies (\operatorname{Nodup}\left(\operatorname{trimmedSums}\left(q\right)\right) \iff \operatorname{Pairwise}\left((a, b \mapsto a > b), \operatorname{tail}\left(q\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/TrimmedAlternatingPartitions.trimmedSums_nodup_iff_strict_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2026). *OEIS A392698*. URL: <https://oeis.org/A392698>.

*Commentary.*

For any positive decreasing list, distinctness is equivalent to strict decrease of its tail. A two-step integer range induction separates the signs and bounds later sums. Equal adjacent tail parts would repeat a sum two positions later. The first two parts may be equal: [2,2,1] qualifies.

**Theorem 1.4 (The corrected partition count).**

$$\forall n: \mathbb{N}, \operatorname{card}\left(\operatorname{filter}\left((p \mapsto \operatorname{Nodup}\left(\operatorname{trimmedSums}\left(\operatorname{sort}\left(\operatorname{parts}\left(p\right), (a, b \mapsto a \ge b)\right)\right)\right)), (\operatorname{univ}\left(\right): \operatorname{Finset}\left(\operatorname{Partition}\left(n\right)\right))\right)\right) = \operatorname{card}\left(\operatorname{distincts}\left(n+1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/TrimmedAlternatingPartitions.card_trimmedSums_eq_distincts` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a392698-trimmed-alternating-partitions` (proved) by `D5/S1/Words/Compositions/TrimmedAlternatingPartitions.card_trimmedSums_eq_distincts`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a392698-trimmed-alternating-partitions","declaration_gid":"D5/S1/Words/Compositions/TrimmedAlternatingPartitions.card_trimmedSums_eq_distincts","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2026). *OEIS A392698*. URL: <https://oeis.org/A392698>.

*Commentary.*

Increase the largest part by one, sending the empty partition to [1]. The strict-tail criterion makes the image a distinct-part partition. The inverse sends [1] to the empty partition and otherwise decreases the maximum by one. Both maps preserve positivity and have the stated weight change; their inverse laws give equality of the two cardinalities for every n, including n=0, where both counts are one.

## References

- Truth anchor: `D5/S1/Words/Compositions/TrimmedAlternatingPartitions.card_trimmedSums_eq_distincts`
- Truth anchor: `D5/S1/Words/Compositions/TrimmedAlternatingPartitions.sumsFrom`
- Truth anchor: `D5/S1/Words/Compositions/TrimmedAlternatingPartitions.trimmedSums`
- Truth anchor: `D5/S1/Words/Compositions/TrimmedAlternatingPartitions.trimmedSums_nodup_iff_strict_tail`
