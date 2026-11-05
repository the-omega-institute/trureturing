# Wiseman A387118

## Abstract

The complemented partition predicates give equal totals.

**Definition 1.1 (Partitions without choosable initial intervals).**

$$\forall (n: \mathbb{N}), \operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(((p: \operatorname{Nat}.\operatorname{Partition}\left(n\right)) \mapsto \neg \operatorname{ChoosableInitial}\left(\operatorname{Multiset}.\operatorname{sort}\left(p.parts, ((a b: \mathbb{N}) \mapsto a \ge b)\right)\right)), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left(\operatorname{Nat}.\operatorname{Partition}\left(n\right)\right))\right)\right)$$

*Formalization.* `D5/S1/Words/Compositions/WisemanA387118.a` (`✓ std3`).

*Citation.* Gus Wiseman (2025). *OEIS A388712, A387118 and A388713*. URL: <https://oeis.org/A388712>.

*Commentary.*

OEIS A387118 counts integer partitions of n without choosable initial intervals. The filter ranges over Nat.Partition n, whose parts are positive, and descending order represents ordinary partitions.

**Definition 1.2 (Nonsuperdiagonal reversed partitions).**

$$\forall (n: \mathbb{N}), \operatorname{nonSuperdiagonal}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(((p: \operatorname{Nat}.\operatorname{Partition}\left(n\right)) \mapsto \neg \operatorname{Superdiagonal}\left(\operatorname{Multiset}.\operatorname{sort}\left(p.parts, ((a b: \mathbb{N}) \mapsto a \le b)\right)\right)), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left(\operatorname{Nat}.\operatorname{Partition}\left(n\right)\right))\right)\right)$$

*Formalization.* `D5/S1/Words/Compositions/WisemanA387118.nonSuperdiagonal` (`✓ std3`).

*Citation.* Gus Wiseman (2025). *OEIS A388712, A387118 and A388713*. URL: <https://oeis.org/A388712>.

*Commentary.*

The conjectured count in OEIS A387118 uses reversed partitions, represented by ascending parts, that fail the one-based weak diagonal bound.

**Definition 1.3 (The conjectured total equality).**

$$claim \iff (\forall (n: \mathbb{N}), \operatorname{a}\left(n\right) = \operatorname{nonSuperdiagonal}\left(n\right))$$

*Formalization.* `D5/S1/Words/Compositions/WisemanA387118.claim` (`✓ std3`).

*Citation.* Gus Wiseman (2025). *OEIS A388712, A387118 and A388713*. URL: <https://oeis.org/A388712>.

*Commentary.*

The two counts are equal for every natural number n, without fixing a further partition statistic.

**Theorem 1.4 (Equality of the total partition counts).**

$$\forall (n: \mathbb{N}), \operatorname{a}\left(n\right) = \operatorname{nonSuperdiagonal}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/WisemanA387118.result` (`✓ std3`). ∎

*Resolves.* `Problems/wiseman-a387118` (proved) by `D5/S1/Words/Compositions/WisemanA387118.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wiseman-a387118","declaration_gid":"D5/S1/Words/Compositions/WisemanA387118.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman (2025). *OEIS A388712, A387118 and A388713*. URL: <https://oeis.org/A388712>.

*Commentary.*

WisemanA388712.sorted_choosable_iff_superdiagonal identifies choosability of descending parts with superdiagonality of ascending parts. Negation gives equal filters on the same finite set of partitions and hence equal cardinalities.

## References

- Truth anchor: `D5/S1/Words/Compositions/WisemanA387118.a`
- Truth anchor: `D5/S1/Words/Compositions/WisemanA387118.claim`
- Truth anchor: `D5/S1/Words/Compositions/WisemanA387118.nonSuperdiagonal`
- Truth anchor: `D5/S1/Words/Compositions/WisemanA387118.result`
- Dependency: [D5/S1/Words/Compositions/ChoosableInitialIntervals](ChoosableInitialIntervals.md)
- Dependency: [D5/S1/Words/Compositions/WisemanA388712](WisemanA388712.md)
