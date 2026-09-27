# The First Schreier-Multiset Recurrence for q = 2

## Abstract

The first q=2 Schreier-multiset counting sequence obeys its conjectured recurrence.

**Definition 1.1 (The ground multiset).**

$$\forall n \in \mathbb{N},\; \operatorname{ground}\left(n\right) = \operatorname{bind}\left(\operatorname{val}\left(\operatorname{Icc}\left(1, n - 1\right)\right), (i \mapsto \operatorname{replicate}\left(2, i\right))\right) + \operatorname{singleton}\left(n\right)$$

*Formalization.* `D5/S1/Recurrence/ChuSchreierMultisetRecurrenceQTwo.ground` (`✓ std3`).

*Citation.* Hùng Việt Chu; Yubo Geng; Julian King; Steven J. Miller; Garrett Tresch; Zachary Louis Vasseur (2026). *Linear Recurrences from Counting Schreier-Type Multisets*. DOI: [10.5281/zenodo.19949535](https://doi.org/10.5281/zenodo.19949535). URL: <https://math.colgate.edu/~integers/aa53/aa53.pdf>.

*Commentary.*

For each natural n, the interval from one through n-1 contributes two copies of every entry, and one distinguished copy of n is added. This is the s=2 ground multiset in the page-19 definition.

**Definition 1.2 (The admissible sub-multisets).**

$$\forall n \in \mathbb{N},\; \operatorname{A}\left(n\right) = \operatorname{filter}\left((F \mapsto (n \in F) \land (\lvert F \rvert \le 2 \cdot \min F)), \operatorname{toFinset}\left(\operatorname{powerset}\left(\operatorname{ground}\left(n\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/ChuSchreierMultisetRecurrenceQTwo.A` (`✓ std3`).

*Citation.* Hùng Việt Chu; Yubo Geng; Julian King; Steven J. Miller; Garrett Tresch; Zachary Louis Vasseur (2026). *Linear Recurrences from Counting Schreier-Type Multisets*. DOI: [10.5281/zenodo.19949535](https://doi.org/10.5281/zenodo.19949535). URL: <https://math.colgate.edu/~integers/aa53/aa53.pdf>.

*Commentary.*

The powerset operation enumerates sub-multisets with multiplicity, so toFinset removes repeated enumerations and yields the finite set of sub-multisets of ground(n). The filter requires n to occur and the multiset cardinality |F| to be at most twice min F. In Lean, min F is F.toFinset.min' with the occurrence of n supplying nonemptiness.

**Definition 1.3 (The counting sequence).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \lvert \operatorname{A}\left(n\right) \rvert$$

*Formalization.* `D5/S1/Recurrence/ChuSchreierMultisetRecurrenceQTwo.a` (`✓ std3`).

*Citation.* Hùng Việt Chu; Yubo Geng; Julian King; Steven J. Miller; Garrett Tresch; Zachary Louis Vasseur (2026). *Linear Recurrences from Counting Schreier-Type Multisets*. DOI: [10.5281/zenodo.19949535](https://doi.org/10.5281/zenodo.19949535). URL: <https://math.colgate.edu/~integers/aa53/aa53.pdf>.

*Commentary.*

The term a(n) is the cardinality of the finite set A(n), hence it counts distinct admissible sub-multisets rather than their repeated occurrences in Multiset.powerset.

**Definition 1.4 (The conjectured recurrence).**

$$(claim) \Leftrightarrow (\forall n \in \mathbb{N},\; (4 \le n) \Rightarrow (\operatorname{a}\left(n\right) = \operatorname{a}\left(n - 1\right) + 2 \cdot \operatorname{a}\left(n - 2\right) + \operatorname{a}\left(n - 3\right)))$$

*Formalization.* `D5/S1/Recurrence/ChuSchreierMultisetRecurrenceQTwo.claim` (`✓ std3`).

*Citation.* Hùng Việt Chu; Yubo Geng; Julian King; Steven J. Miller; Garrett Tresch; Zachary Louis Vasseur (2026). *Linear Recurrences from Counting Schreier-Type Multisets*. DOI: [10.5281/zenodo.19949535](https://doi.org/10.5281/zenodo.19949535). URL: <https://math.colgate.edu/~integers/aa53/aa53.pdf>.

*Commentary.*

The source does not print a starting index. The statement begins at four, the least index for which n, n-1, n-2, and n-3 all lie in the sequence indexed from one. Subtraction is truncated natural-number subtraction, and under 4<=n it agrees with the displayed indices.

**Theorem 1.5 (The recurrence).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/ChuSchreierMultisetRecurrenceQTwo.result` (`✓ std3`). ∎

*Resolves.* `Problems/chu-2026-schreier-multiset-recurrence-q-two` (proved) by `D5/S1/Recurrence/ChuSchreierMultisetRecurrenceQTwo.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"chu-2026-schreier-multiset-recurrence-q-two","declaration_gid":"D5/S1/Recurrence/ChuSchreierMultisetRecurrenceQTwo.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Hùng Việt Chu; Yubo Geng; Julian King; Steven J. Miller; Garrett Tresch; Zachary Louis Vasseur (2026). *Linear Recurrences from Counting Schreier-Type Multisets*. DOI: [10.5281/zenodo.19949535](https://doi.org/10.5281/zenodo.19949535). URL: <https://math.colgate.edu/~integers/aa53/aa53.pdf>.

*Commentary.*

Admissible sub-multisets are put in bijection with the disjoint union of ordered compositions of 2n-2 and 2n-1 whose parts are 2, 3, or 4. Removing the first part gives the composition recurrence with shifts 2, 3, and 4; applying it to the four adjacent counting terms gives the stated recurrence.

## References

- Truth anchor: `D5/S1/Recurrence/ChuSchreierMultisetRecurrenceQTwo.A`
- Truth anchor: `D5/S1/Recurrence/ChuSchreierMultisetRecurrenceQTwo.a`
- Truth anchor: `D5/S1/Recurrence/ChuSchreierMultisetRecurrenceQTwo.claim`
- Truth anchor: `D5/S1/Recurrence/ChuSchreierMultisetRecurrenceQTwo.ground`
- Truth anchor: `D5/S1/Recurrence/ChuSchreierMultisetRecurrenceQTwo.result`
