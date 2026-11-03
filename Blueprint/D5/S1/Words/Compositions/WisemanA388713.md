# Wiseman A388713

## Abstract

The partition predicates give equal counts with a fixed maximum.

**Definition 1.1 (Superdiagonal reversed partitions by maximum).**

$$\forall (n: \mathbb{N}), \forall (k: \mathbb{N}), \operatorname{T}\left(n, k\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(((p: \operatorname{Nat}.\operatorname{Partition}\left(n\right)) \mapsto \operatorname{Multiset}.\operatorname{sup}\left(p.parts\right) = k \land \operatorname{Superdiagonal}\left(\operatorname{Multiset}.\operatorname{sort}\left(p.parts, ((a b: \mathbb{N}) \mapsto a \le b)\right)\right)), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left(\operatorname{Nat}.\operatorname{Partition}\left(n\right)\right))\right)\right)$$

*Formalization.* `D5/S1/Words/Compositions/WisemanA388713.T` (`✓ std3`).

*Citation.* Gus Wiseman (2025). *OEIS A388712, A387118 and A388713*. URL: <https://oeis.org/A388712>.

*Commentary.*

OEIS A388713 counts superdiagonal multisets summing to n with maximum k. Ascending parts represent reversed partitions, the weak diagonal bound uses index plus one, and Multiset.sup supplies the maximum.

**Definition 1.2 (Choosable partitions by maximum).**

$$\forall (n: \mathbb{N}), \forall (k: \mathbb{N}), \operatorname{choosable}\left(n, k\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(((p: \operatorname{Nat}.\operatorname{Partition}\left(n\right)) \mapsto \operatorname{Multiset}.\operatorname{sup}\left(p.parts\right) = k \land \operatorname{ChoosableInitial}\left(\operatorname{Multiset}.\operatorname{sort}\left(p.parts, ((a b: \mathbb{N}) \mapsto a \ge b)\right)\right)), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left(\operatorname{Nat}.\operatorname{Partition}\left(n\right)\right))\right)\right)$$

*Formalization.* `D5/S1/Words/Compositions/WisemanA388713.choosable` (`✓ std3`).

*Citation.* Gus Wiseman (2025). *OEIS A388712, A387118 and A388713*. URL: <https://oeis.org/A388712>.

*Commentary.*

The conjectured count in OEIS A388713 uses partitions of n with maximum k and choosable initial intervals. The empty partition has maximum zero and satisfies both predicates, so both formal counts are 1 at (0,0); the printed source row is 0.

**Definition 1.3 (The conjectured maximum-refined equality).**

$$claim \iff (\forall (n: \mathbb{N}), \forall (k: \mathbb{N}), \operatorname{T}\left(n, k\right) = \operatorname{choosable}\left(n, k\right))$$

*Formalization.* `D5/S1/Words/Compositions/WisemanA388713.claim` (`✓ std3`).

*Citation.* Gus Wiseman (2025). *OEIS A388712, A387118 and A388713*. URL: <https://oeis.org/A388712>.

*Commentary.*

For every pair of natural numbers n and k, the superdiagonal reversed-partition count equals the choosable partition count with the same maximum.

**Theorem 1.4 (Equality of the partition counts by maximum).**

$$\forall (n: \mathbb{N}), \forall (k: \mathbb{N}), \operatorname{T}\left(n, k\right) = \operatorname{choosable}\left(n, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/WisemanA388713.result` (`✓ std3`). ∎

*Resolves.* `Problems/wiseman-a388713` (proved) by `D5/S1/Words/Compositions/WisemanA388713.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wiseman-a388713","declaration_gid":"D5/S1/Words/Compositions/WisemanA388713.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman (2025). *OEIS A388712, A387118 and A388713*. URL: <https://oeis.org/A388712>.

*Commentary.*

WisemanA388712.sorted_choosable_iff_superdiagonal identifies the two predicates. Its reverse direction and the common maximum-part condition give identical filters, whose cardinalities agree.

## References

- Truth anchor: `D5/S1/Words/Compositions/WisemanA388713.T`
- Truth anchor: `D5/S1/Words/Compositions/WisemanA388713.choosable`
- Truth anchor: `D5/S1/Words/Compositions/WisemanA388713.claim`
- Truth anchor: `D5/S1/Words/Compositions/WisemanA388713.result`
- Dependency: [D5/S1/Words/Compositions/ChoosableInitialIntervals](ChoosableInitialIntervals.md)
- Dependency: [D5/S1/Words/Compositions/WisemanA388712](WisemanA388712.md)
