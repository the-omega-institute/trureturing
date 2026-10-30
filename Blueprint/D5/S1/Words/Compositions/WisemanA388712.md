# Wiseman A388712

## Abstract

The two partition predicates give equal counts.

**Definition 1.1 (Partitions without choosable initial intervals).**

$$\forall (n: \mathbb{N}), \forall (k: \mathbb{N}), \operatorname{T}\left(n, k\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(((p: \operatorname{Nat}.\operatorname{Partition}\left(n\right)) \mapsto \operatorname{Multiset}.\operatorname{card}\left(p.parts\right) = k \land \neg \operatorname{ChoosableInitial}\left(\operatorname{Multiset}.\operatorname{sort}\left(p.parts, ((a b: \mathbb{N}) \mapsto a \ge b)\right)\right)), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left(\operatorname{Nat}.\operatorname{Partition}\left(n\right)\right))\right)\right)$$

*Formalization.* `D5/S1/Words/Compositions/WisemanA388712.T` (`✓ std3`).

*Citation.* Gus Wiseman (2025). *OEIS A388712, A387118 and A388713*. URL: <https://oeis.org/A388712>.

*Commentary.*

Triangle read by rows where T(n,k) is the number of integer partitions of n into k parts without choosable initial intervals. OEIS A388712, Name (unpaginated). The counts range over Nat.Partition n, whose parts are positive. Descending order represents ordinary partitions; ascending order represents reversed partitions. List indices start at zero, so Superdiagonal uses i+1.

**Definition 1.2 (Nonsuperdiagonal reversed partitions).**

$$\forall (n: \mathbb{N}), \forall (k: \mathbb{N}), \operatorname{nonSuperdiagonal}\left(n, k\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(((p: \operatorname{Nat}.\operatorname{Partition}\left(n\right)) \mapsto \operatorname{Multiset}.\operatorname{card}\left(p.parts\right) = k \land \neg \operatorname{Superdiagonal}\left(\operatorname{Multiset}.\operatorname{sort}\left(p.parts, ((a b: \mathbb{N}) \mapsto a \le b)\right)\right)), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left(\operatorname{Nat}.\operatorname{Partition}\left(n\right)\right))\right)\right)$$

*Formalization.* `D5/S1/Words/Compositions/WisemanA388712.nonSuperdiagonal` (`✓ std3`).

*Citation.* Gus Wiseman (2025). *OEIS A388712, A387118 and A388713*. URL: <https://oeis.org/A388712>.

*Commentary.*

Conjecture: Also the number of non-superdiagonal reversed partitions of n into k parts, where a sequence (y_1, ..., y_k) is superdiagonal iff y_i >= i for all i = 1..k. OEIS A388712, Comments (unpaginated). The counts range over Nat.Partition n, whose parts are positive. Descending order represents ordinary partitions; ascending order represents reversed partitions. List indices start at zero, so Superdiagonal uses i+1.

**Definition 1.3 (The conjectured equality).**

$$claim \iff (\forall (n: \mathbb{N}), \forall (k: \mathbb{N}), \operatorname{T}\left(n, k\right) = \operatorname{nonSuperdiagonal}\left(n, k\right))$$

*Formalization.* `D5/S1/Words/Compositions/WisemanA388712.claim` (`✓ std3`).

*Citation.* Gus Wiseman (2025). *OEIS A388712, A387118 and A388713*. URL: <https://oeis.org/A388712>.

*Commentary.*

Conjecture: Also the number of non-superdiagonal reversed partitions of n into k parts, where a sequence (y_1, ..., y_k) is superdiagonal iff y_i >= i for all i = 1..k. OEIS A388712, Comments (unpaginated). The equality quantifies over every pair of naturals n and k.

**Lemma 1.4 (The two sort orders).**

$$\forall (s: \operatorname{Multiset}\left(\mathbb{N}\right)), \operatorname{ChoosableInitial}\left(\operatorname{Multiset}.\operatorname{sort}\left(s, ((a b: \mathbb{N}) \mapsto a \ge b)\right)\right) \iff \operatorname{Superdiagonal}\left(\operatorname{Multiset}.\operatorname{sort}\left(s, ((a b: \mathbb{N}) \mapsto a \le b)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/WisemanA388712.sorted_choosable_iff_superdiagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every multiset of naturals, choosability of the descending list is equivalent to superdiagonality of the ascending list. Permutation invariance and the increasing-list criterion prove the equivalence, including the empty multiset and multisets containing zeros. All three partition identities use it.

**Theorem 1.5 (Equality of the partition counts).**

$$\forall (n: \mathbb{N}), \forall (k: \mathbb{N}), \operatorname{T}\left(n, k\right) = \operatorname{nonSuperdiagonal}\left(n, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/WisemanA388712.result` (`✓ std3`). ∎

*Resolves.* `Problems/wiseman388-partitions` (proved) by `D5/S1/Words/Compositions/WisemanA388712.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wiseman388-partitions","declaration_gid":"D5/S1/Words/Compositions/WisemanA388712.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman (2025). *OEIS A388712, A387118 and A388713*. URL: <https://oeis.org/A388712>.

*Commentary.*

The two filters have the same truth value on each partition, so their finite cardinalities agree. The sorted-list equivalence identifies the predicates under negation and preserves the number of parts.

## References

- Truth anchor: `D5/S1/Words/Compositions/WisemanA388712.T`
- Truth anchor: `D5/S1/Words/Compositions/WisemanA388712.claim`
- Truth anchor: `D5/S1/Words/Compositions/WisemanA388712.nonSuperdiagonal`
- Truth anchor: `D5/S1/Words/Compositions/WisemanA388712.result`
- Truth anchor: `D5/S1/Words/Compositions/WisemanA388712.sorted_choosable_iff_superdiagonal`
- Dependency: [D5/S1/Words/Compositions/ChoosableInitialIntervals](ChoosableInitialIntervals.md)
