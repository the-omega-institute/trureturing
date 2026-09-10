# Zero-Prepended First Sums and Odd Parts

## Abstract

Zero-prepended first sums of increasing positive lists correspond to odd-part partitions.

OEIS A392694 concerns reversed partitions, meaning positive parts in weakly increasing order. The zero-based alternating recurrence starts at s0=0 and satisfies yj=s(j-1)+sj. The source condition is expressed by an increasing positive preimage under the existing adjacent-sums definition. The empty list is included. All counts below range over partitions of n.

**Definition 1.1 (The source predicate).**

$$\forall y: \operatorname{List}\left(\mathbb{N}\right), \operatorname{IsZeroPrependedFirstSums}\left(y\right) \iff (\exists s: \operatorname{List}\left(\mathbb{N}\right), \operatorname{Pairwise}\left((a, b \mapsto a \le b), s\right) \land (\forall x: \mathbb{N}, x \in s \implies 0 < x) \land \operatorname{firstSums}\left(\operatorname{cons}\left(0, s\right)\right) = y)$$

*Formalization.* `D5/S1/Words/Compositions/ZeroPrependedFirstSumsOddParts.IsZeroPrependedFirstSums` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2026). *OEIS A392694*. URL: <https://oeis.org/A392694>.

*Commentary.*

There exists a weakly increasing positive list s whose adjacent sums after prepending zero equal y. Fixed-start adjacent sums are injective. The image is automatically positive and weakly increasing. No truncated alternating subtraction is used in this definition.

**Theorem 1.2 (The odd-parts correspondence).**

$$\forall n: \mathbb{N}, \operatorname{card}\left(\operatorname{filter}\left((p \mapsto \operatorname{IsZeroPrependedFirstSums}\left(\operatorname{sort}\left(\operatorname{parts}\left(p\right), (a, b \mapsto a \le b)\right)\right)), (\operatorname{univ}\left(\right): \operatorname{Finset}\left(\operatorname{Partition}\left(n\right)\right))\right)\right) = \operatorname{card}\left(\operatorname{odds}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/ZeroPrependedFirstSumsOddParts.card_zeroPrependedFirstSums_eq_odds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2026). *OEIS A392694*. URL: <https://oeis.org/A392694>.

*Commentary.*

Reverse s into the positive row lengths of a Young diagram, transpose, and replace each column height h by 2h-1. This is an equivalence: odd parts recover heights by (x+1)/2, and transposition is involutive. The first-sums sum identity and the column identity prove preservation of weight. Positive row lengths exclude zero padding. Sorting transports the equivalence to Mathlib partitions of each n.

**Theorem 1.3 (The A000009 count).**

$$\forall n: \mathbb{N}, \operatorname{card}\left(\operatorname{filter}\left((p \mapsto \operatorname{IsZeroPrependedFirstSums}\left(\operatorname{sort}\left(\operatorname{parts}\left(p\right), (a, b \mapsto a \le b)\right)\right)), (\operatorname{univ}\left(\right): \operatorname{Finset}\left(\operatorname{Partition}\left(n\right)\right))\right)\right) = \operatorname{card}\left(\operatorname{distincts}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/ZeroPrependedFirstSumsOddParts.card_zeroPrependedFirstSums_eq_distincts` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a392694-zero-prepended-first-sums` (proved) by `D5/S1/Words/Compositions/ZeroPrependedFirstSumsOddParts.card_zeroPrependedFirstSums_eq_distincts`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a392694-zero-prepended-first-sums","declaration_gid":"D5/S1/Words/Compositions/ZeroPrependedFirstSumsOddParts.card_zeroPrependedFirstSums_eq_distincts","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2026). *OEIS A392694*. URL: <https://oeis.org/A392694>.

*Commentary.*

Compose the new odd-parts counting theorem with Mathlib's Nat.Partition.card_odds_eq_card_distincts. Thus the source count is A000009(n), without a shift. At n=0 both sides count the single empty partition. Euler's theorem is reused, not reproved.

## References

- Truth anchor: `D5/S1/Words/Compositions/ZeroPrependedFirstSumsOddParts.IsZeroPrependedFirstSums`
- Truth anchor: `D5/S1/Words/Compositions/ZeroPrependedFirstSumsOddParts.card_zeroPrependedFirstSums_eq_distincts`
- Truth anchor: `D5/S1/Words/Compositions/ZeroPrependedFirstSumsOddParts.card_zeroPrependedFirstSums_eq_odds`
- Dependency: [D5/S1/Words/Compositions/FirstSumsPartitionCharacterization](FirstSumsPartitionCharacterization.md)
