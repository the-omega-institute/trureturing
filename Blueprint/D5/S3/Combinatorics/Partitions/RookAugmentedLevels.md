# Actual augmented Ferrers levels

## Abstract

Actual augmented completions prove native factorization, exact root multiplicities, and singleton level data for arbitrary Ferrers input.

**Definition 1.1 (Disjoint source and auxiliary columns).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.Columns`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.Columns` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Columns(B,t) is the disjoint sum of the original positive-column positions and t auxiliary positions. Original and auxiliary columns can never be confused by their labels.

**Definition 1.2 (Literal augmented cells).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.level`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.level` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For N levels indexed from the top, position p has bottom-up index N-1-p. An original column i contributes exactly the within-level rows r with m(N-1-p)+r below its actual source height. Every auxiliary column contributes all m within-level rows. For lengths below the board's full height, this definition counts its actual first N bottom-up levels; the registered common lengths cover the whole board.

**Theorem 1.3 (The level-total product on actual cells).**

$$\forall m \in Nat,\; \forall n \in Nat,\; \forall t \in Nat,\; \forall b \in PositiveColumns,\; \operatorname{card}\left(\operatorname{Selections}\left(m, \operatorname{level}\left(m, n, t, b\right)\right)\right) = \operatorname{levelProduct}\left(m, n, t, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.augmented_selections_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m,N,t and every normalized original board B, the number of full Selections of the actual augmented levels equals levelProduct(m,N,t,B). This product ranges over i in Fin(N), with factor columnLevel(m,B,N-1-i) plus mt minus mi in natural truncated subtraction. No singleton hypothesis is used. If a column contains a cell in an upper level, bottom justification gives all m cells in that column in a lower level. Auxiliary columns are full by construction. The generic selections_count theorem therefore applies, and a direct finite cell count identifies each level cardinality with columnLevel plus mt.

**Theorem 1.4 (Native placement and completion bijection).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.native_completion_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.native_completion_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive m, every normalized original board B, every N at least area(B)+1, and every natural t, the same augmented selection count equals the sum for k from zero through N of rookCount(m,B,k) times m^(N-k) times the descending factorial of t of length N-k. Partial records retain precisely the original coordinates at their actual levels. completionEquiv reversibly fills their vacant levels with an embedding into the t auxiliary columns and an independent Fin(m) row function. nativePartialEquiv transports those records to literal Nonattacking cell subsets. It uses row=m(N-1-i)+r, quotient and remainder, and the source-column reflection c.rev. Its inverse recovers every original cell using the area bound; equal native levels force equal chosen cells. Stratification by the actual subset cardinality gives rookCount, and Fintype.card_embedding_eq supplies the descending factorial, including impossible-capacity cases.

**Theorem 1.5 (Same-board polynomial factorization).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.native_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.native_factorization` (`✓ std3`). ∎

*Citation.* Kenneth Barrese, Nicholas Loehr, Jeffrey Remmel, Bruce E. Sagan (2015). *Bijections on m-level Rook Placements*. DOI: [10.1016/j.ejc.2016.03.005](https://doi.org/10.1016/j.ejc.2016.03.005). URL: <https://arxiv.org/abs/1508.05944v1>.

*Commentary.*

rookPolynomial(m,N,B) is the sum of C(rookCount(m,B,k) m^(N-k)) times the descending Pochhammer polynomial of degree N-k. levelPolynomial(m,N,B) is the product of C(columnLevel(m,B,N-1-i)) + C(m) X - C(mi). This is Barrese, Loehr, Remmel and Sagan, arXiv:1508.05944v1 §6.1, Theorem 26 at x=mt. The source takes N at least the width and the number of nonempty levels. For positive m the Lean identity uses the stronger common bound N at least area(B)+1. Its proof counts the same selections through the native Lean bijections completionEquiv and nativePartialEquiv. Both evaluations count the same augmented selections at every integer t=N+n. At those values each natural subtraction is justified by mi at most mt, so casting preserves each product factor. Polynomial.eq_of_infinite_eval_eq gives the identity on the same original board.

**Definition 1.6 (Actual original choices at fixed levels).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.Partial`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.Partial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A Partial is an option-valued function on Fin(N). A present value retains the actual source column and within-level row, satisfies the source-height inequality, and uses a column at most once across levels.

**Definition 1.7 (The exact complement of occupied levels).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.Vacant`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.Vacant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Vacant(p) is the subtype of levels where the partial function is none. Its cardinality is N minus the actual native subset cardinality.

**Definition 1.8 (Reversible auxiliary completion).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.completionEquiv`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.completionEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The dependent sum of Partial p, an embedding Vacant(p) into Fin(t), and a function Vacant(p) into Fin(m) is equivalent to the exact Selections type on the augmented levels. Both composites are identities.

**Definition 1.9 (Native coordinates with reflection).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.nativeCoord`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.nativeCoord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A level i and source cell (c,r) map to the literal pair (m(N-1-i)+r,c.rev). Positive m makes this coordinate map injective; the area-based common length makes it cover every source cell.

**Definition 1.10 (Unstratified native subsets).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.NativePlacements`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.NativePlacements` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the subtype of the powerset of the genuine cells(B) satisfying the exact Nonattacking(m) predicate, before a subset size is selected.

**Definition 1.11 (Reversible transport to genuine subsets).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.nativePartialEquiv`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.nativePartialEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For positive m and N at least area(B)+1, nativePartialEquiv identifies Partial with NativePlacements. It proves membership, nonattacking legality and both inverse laws on the actual cell coordinates.

**Definition 1.12 (Native falling-factorial expansion).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.rookPolynomial`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.rookPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum over k from zero through N of C(rookCount(m,B,k) m^(N-k)) times descPochhammer over the integers of degree N-k.

**Definition 1.13 (Same-board level product).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.levelPolynomial`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.levelPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Product over i in Fin(N) of C(columnLevel(m,B,N-1-i)) + C(m) X - C(mi). Integer subtraction has no truncation.

**Definition 1.14 (Actual level roots).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.levelRoots`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.levelRoots` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer at i is mi minus columnLevel(m,B,N-1-i). RookClassCandidate identifies this exact function with the registered seedRoots at every registered common length.

**Theorem 1.15 (Native equivalence and equality of level products).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.rookEquivalent_iff_levelPolynomial`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.rookEquivalent_iff_levelPolynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive m and a common N at least area(A)+1 and area(B)+1, RookEquivalent(m,A,B) holds exactly when their levelPolynomials agree. Descending Pochhammer polynomials form a polynomial sequence with distinct degrees. Linear independence recovers each rook coefficient through N, and the positive factor m^(N-k) cancels. Counts above N vanish by the actual area bound.

**Theorem 1.16 (Exact root multiplicities).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.levelPolynomial_eq_iff_roots`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.levelPolynomial_eq_iff_roots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive m, every N and arbitrary normalized A,B, equality of levelPolynomials is equivalent to permutation equality of their complete levelRoots lists. Substitution by mX is injective, as shown by infinitely many distinct integer multiples of m. Roots of the product of X minus each root recover the full multiset, preserving repeated entries.

**Theorem 1.17 (The actual level tuple is singleton).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.level_totals_singleton`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.level_totals_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive m, any N and arbitrary normalized B, the top-down level-total function is SingletonColumns. The original B need not be singleton. If an upper level occupies c columns, its cardinality is at most mc, while every lower level contains all mc cells of those columns. A nonmultiple upper total is strictly below mc, forcing a strict increase of quotient before another partial total can have that quotient.

**Theorem 1.18 (Level totals preserve the actual area).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.level_totals_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.level_totals_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive m and every N at least area(B)+1, the sum over all N top-down columnLevel totals is area(B). An explicit finite bijection maps every valid level, source column and row triple to the genuine cells(B); row division and remainder and the reflected source column give its inverse.

These are symbolic results for arbitrary boards, including the empty board. They supply the native class identification in RookClassCandidate. The exact registered UniversalFormula and weight Q are unchanged. The proofs reuse the pinned Mathlib embedding cardinality, descending Pochhammer sequence and root-product identities. In arXiv:1508.05944v1, §6.1 gives the factorization and §6.2 asks for the whole-class count. The admissibility test for singleton root vectors is Proposition 4.4 of arXiv:1308.4081v1.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.Columns`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.NativePlacements`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.Partial`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.Vacant`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.augmented_selections_count`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.completionEquiv`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.level`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.levelPolynomial`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.levelPolynomial_eq_iff_roots`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.levelRoots`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.level_totals_singleton`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.level_totals_sum`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.nativeCoord`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.nativePartialEquiv`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.native_completion_count`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.native_factorization`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.rookEquivalent_iff_levelPolynomial`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookAugmentedLevels.rookPolynomial`
- Dependency: [D5/S3/Combinatorics/Partitions/RookLevelSelection](RookLevelSelection.md)
- Dependency: [D5/S3/Combinatorics/Partitions/RookRootCriterion](RookRootCriterion.md)
