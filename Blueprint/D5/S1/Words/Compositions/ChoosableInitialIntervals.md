# Choosable Initial Intervals

## Abstract

Distinct representatives of increasing initial intervals exist exactly above the diagonal.

OEIS A388711 compares partitions with choosable initial intervals and superdiagonal reversed partitions. Ordinary parts are sorted decreasingly; reversed parts are sorted increasingly. Indices below start at zero, so the diagonal condition contains i+1. All parts and representatives are naturals.

**Definition 1.1 (Distinct positive representatives).**

$$\forall l: \operatorname{List}\left(\mathbb{N}\right), \operatorname{ChoosableInitial}\left(l\right) \iff (\exists f: \operatorname{Fin}\left(\operatorname{length}\left(l\right)\right) \Rightarrow \mathbb{N}, \operatorname{Injective}\left(f\right) \land (\forall i: \operatorname{Fin}\left(\operatorname{length}\left(l\right)\right), 1 \le \operatorname{f}\left(i\right) \land \operatorname{f}\left(i\right) \le \operatorname{get}\left(l, i\right)))$$

*Formalization.* `D5/S1/Words/Compositions/ChoosableInitialIntervals.ChoosableInitial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2025). *OEIS A388711*. URL: <https://oeis.org/A388711>.

*Commentary.*

A representative is chosen at each list position, is at least one, and is at most that position's part. Injectivity makes the choices distinct. A zero part has no allowed choice; the empty family is choosable.

**Definition 1.2 (The diagonal condition).**

$$\forall l: \operatorname{List}\left(\mathbb{N}\right), \operatorname{Superdiagonal}\left(l\right) \iff (\forall i: \operatorname{Fin}\left(\operatorname{length}\left(l\right)\right), i + 1 \le \operatorname{get}\left(l, i\right))$$

*Formalization.* `D5/S1/Words/Compositions/ChoosableInitialIntervals.Superdiagonal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2025). *OEIS A388711*. URL: <https://oeis.org/A388711>.

*Commentary.*

The part at zero-based position i is at least i+1. The list theorem does not assume positivity; the condition itself implies it.

**Lemma 1.3 (Order invariance).**

$$\forall l: \operatorname{List}\left(\mathbb{N}\right), \forall m: \operatorname{List}\left(\mathbb{N}\right), \operatorname{Perm}\left(l, m\right) \implies (\operatorname{ChoosableInitial}\left(l\right) \iff \operatorname{ChoosableInitial}\left(m\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/ChoosableInitialIntervals.choosableInitial_congr_perm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2025). *OEIS A388711*. URL: <https://oeis.org/A388711>.

*Commentary.*

Represent the choice map as a nodup list related positionwise to the parts. Mathlib's relational permutation lemma transports that list and preserves nodup. Thus choosability depends only on the multiset of parts.

**Theorem 1.4 (The initial-interval criterion).**

$$\forall l: \operatorname{List}\left(\mathbb{N}\right), \operatorname{Pairwise}\left((a, b \mapsto a \le b), l\right) \implies (\operatorname{ChoosableInitial}\left(l\right) \iff \operatorname{Superdiagonal}\left(l\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/ChoosableInitialIntervals.choosableInitial_iff_superdiagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2025). *OEIS A388711*. URL: <https://oeis.org/A388711>.

*Commentary.*

Restrict the injection to the first i+1 positions. Monotonicity bounds all these positive representatives by the part at i. Subtracting one gives an injection Fin(i+1) into Fin(l[i]); finite cardinal comparison proves the bound. In the other direction choose i+1. This elementary criterion is not claimed as a new mathematical theorem or a new form of Hall's theorem.

**Theorem 1.5 (Equality of the two partition counts).**

$$\forall n: \mathbb{N}, \forall k: \mathbb{N}, \operatorname{card}\left(\operatorname{filter}\left((p \mapsto \operatorname{card}\left(\operatorname{parts}\left(p\right)\right) = k \land ChoosableInitial\left(\operatorname{sort}\left(\operatorname{parts}\left(p\right), (a, b \mapsto a \ge b)\right)\right)), (\operatorname{univ}\left(\right): \operatorname{Finset}\left(\operatorname{Partition}\left(n\right)\right))\right)\right) = \operatorname{card}\left(\operatorname{filter}\left((p \mapsto \operatorname{card}\left(\operatorname{parts}\left(p\right)\right) = k \land Superdiagonal\left(\operatorname{sort}\left(\operatorname{parts}\left(p\right), (a, b \mapsto a \le b)\right)\right)), (\operatorname{univ}\left(\right): \operatorname{Finset}\left(\operatorname{Partition}\left(n\right)\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/ChoosableInitialIntervals.card_choosable_eq_superdiagonal` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a388711-choosable-initial-intervals` (proved) by `D5/S1/Words/Compositions/ChoosableInitialIntervals.card_choosable_eq_superdiagonal`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a388711-choosable-initial-intervals","declaration_gid":"D5/S1/Words/Compositions/ChoosableInitialIntervals.card_choosable_eq_superdiagonal","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2025). *OEIS A388711*. URL: <https://oeis.org/A388711>.

*Commentary.*

Both filters range over Mathlib's partitions of n and require exactly k positive parts. Order invariance relates descending and ascending order; the initial-interval criterion then identifies the predicates. The equality holds for all n and k, including the empty partition at n=k=0.

## References

- Truth anchor: `D5/S1/Words/Compositions/ChoosableInitialIntervals.ChoosableInitial`
- Truth anchor: `D5/S1/Words/Compositions/ChoosableInitialIntervals.Superdiagonal`
- Truth anchor: `D5/S1/Words/Compositions/ChoosableInitialIntervals.card_choosable_eq_superdiagonal`
- Truth anchor: `D5/S1/Words/Compositions/ChoosableInitialIntervals.choosableInitial_congr_perm`
- Truth anchor: `D5/S1/Words/Compositions/ChoosableInitialIntervals.choosableInitial_iff_superdiagonal`
