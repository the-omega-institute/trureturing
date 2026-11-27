# Hardin's constant-stress rectangular arrays

## Abstract

Hardin's common six-lag recurrence for constant-stress rectangular arrays.

**Definition 1.1 (Rectangular arrays).**

$$\forall n: Nat, (\forall k: Nat, (\operatorname{Grid}\left(n, k\right) = (\operatorname{Fin}\left(n + 1\right) \to \operatorname{Fin}\left(k + 1\right) \to \operatorname{Fin}\left(4\right))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.Grid` (`✓ std3`).

*Citation.* R. H. Hardin (2014). *OEIS A235289 — Constant-stress rectangular arrays*. URL: <https://oeis.org/A235289>.

*Commentary.*

The alphabet has four entries, 0 through 3. Indices start at zero, so a grid indexed by n and k has n+1 rows and k+1 columns.

**Definition 1.2 (The contiguous block condition).**

$$\forall n: Nat, (\forall k: Nat, (\forall A: \operatorname{Grid}\left(n, k\right), ((\operatorname{Legal}\left(A\right)) \iff (\forall i: \operatorname{Fin}\left(n\right), (\forall j: \operatorname{Fin}\left(k\right), (\operatorname{Int.natAbs}\left(((\operatorname{val}\left(A\left(\operatorname{Fin.castSucc}\left(i\right), \operatorname{Fin.castSucc}\left(j\right)\right)\right): Int) + (\operatorname{val}\left(A\left(\operatorname{Fin.succ}\left(i\right), \operatorname{Fin.succ}\left(j\right)\right)\right): Int)) - ((\operatorname{val}\left(A\left(\operatorname{Fin.castSucc}\left(i\right), \operatorname{Fin.succ}\left(j\right)\right)\right): Int) + (\operatorname{val}\left(A\left(\operatorname{Fin.succ}\left(i\right), \operatorname{Fin.castSucc}\left(j\right)\right)\right): Int))\right) = 4))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.Legal` (`✓ std3`).

*Citation.* R. H. Hardin (2014). *OEIS A235289 — Constant-stress rectangular arrays*. URL: <https://oeis.org/A235289>.

*Commentary.*

Each pair of indices selects the upper left corner of one contiguous block. Fin.castSucc preserves the index and Fin.succ increments it, both in the larger index type. The condition uses the natural absolute value of the difference of the diagonal and antidiagonal sums after casting the entries to integers.

**Definition 1.3 (The literal rectangular count).**

$$\forall n: Nat, (\forall k: Nat, (\operatorname{T}\left(n, k\right) = (\operatorname{Nat.card}\left(\{A: \operatorname{Grid}\left(n, k\right) \mid \operatorname{Legal}\left(A\right)\}\right): Int)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.T` (`✓ std3`).

*Citation.* R. H. Hardin (2014). *OEIS A235289 — Constant-stress rectangular arrays*. URL: <https://oeis.org/A235289>.

*Commentary.*

The cardinality counts every legal filling in its given orientation. It is viewed as an integer for the signed recurrence.

**Theorem 1.4 (The common six-lag recurrence).**

$$\forall d: Nat \times Nat, ((0 < d.1) \implies ((0 < d.2) \implies ((\operatorname{T}\left(d.1 + 6, d.2\right) = 3 \cdot \operatorname{T}\left(d.1 + 5, d.2\right) + 3 \cdot \operatorname{T}\left(d.1 + 4, d.2\right) - 15 \cdot \operatorname{T}\left(d.1 + 3, d.2\right) + 4 \cdot \operatorname{T}\left(d.1 + 2, d.2\right) + 18 \cdot \operatorname{T}\left(d.1 + 1, d.2\right) - 12 \cdot \operatorname{T}\left(d.1, d.2\right)) \land (\operatorname{T}\left(d.1, d.2 + 6\right) = 3 \cdot \operatorname{T}\left(d.1, d.2 + 5\right) + 3 \cdot \operatorname{T}\left(d.1, d.2 + 4\right) - 15 \cdot \operatorname{T}\left(d.1, d.2 + 3\right) + 4 \cdot \operatorname{T}\left(d.1, d.2 + 2\right) + 18 \cdot \operatorname{T}\left(d.1, d.2 + 1\right) - 12 \cdot \operatorname{T}\left(d.1, d.2\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin-a235289-common-recurrence` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin-a235289-common-recurrence","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2014). *OEIS A235289 — Constant-stress rectangular arrays*. URL: <https://oeis.org/A235289>.

*Commentary.*

OEIS A235289 proposes a common recurrence for every row and every column. The pair d gives the row and column indices of the table. Either varying index starts at seven, since the smallest lagged index in each displayed identity is positive.

Complementing every cell on one checkerboard color converts the diagonal difference into a block sum of two or ten. Adjacent blocks share two cells. Their sums can differ by at most six, so every block has the same sum. Complementing all cells exchanges the two classes.

For a sum-two array, the horizontal adjacent sums in successive rows alternate between a profile and its complement in two. If the first edge sum is s, the initial entry can range from 0 to s, giving at most s+1 choices. The complement has first edge sum 2−s, giving at most 3−s initial choices. The initial entry determines the row from its adjacent sums, so the profile and its complement have at most four row choices in total. The nonzero contributions have one-step multiplier one or two, or two-step multiplier two or three. Each contribution satisfies the displayed recurrence, and summing the contributions proves the first identity. Transposition gives the second.

**Lemma 1.5 (Adjacent equality on a finite interval).**

$$\forall n: Nat, (\forall A: Type, (\forall f: \operatorname{Fin}\left(n + 1\right) \to A, ((\forall j: \operatorname{Fin}\left(n\right), (f\left(\operatorname{Fin.castSucc}\left(j\right)\right) = f\left(\operatorname{Fin.succ}\left(j\right)\right))) \implies (\forall i: \operatorname{Fin}\left(n + 1\right), (f\left(i\right) = f\left(0\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.fin_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a function agrees at each adjacent pair, its value at every index is its value at zero.

**Definition 1.6 (Row profiles).**

$$\forall k: Nat, (\operatorname{Profile}\left(k\right) = (\operatorname{Fin}\left(k\right) \to \operatorname{Fin}\left(3\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.Profile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A profile assigns one of 0, 1 or 2 to each of the k horizontal edges of a row with k+1 cells.

**Definition 1.7 (Adjacent entry sum).**

$$\forall k: Nat, (\forall r: \operatorname{Fin}\left(k + 1\right) \to \operatorname{Fin}\left(4\right), (\forall j: \operatorname{Fin}\left(k\right), (\operatorname{edge}\left(r, j\right) = \operatorname{val}\left(r\left(\operatorname{Fin.castSucc}\left(j\right)\right)\right) + \operatorname{val}\left(r\left(\operatorname{Fin.succ}\left(j\right)\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.edge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every row uses the alphabet 0 through 3. The sum at an edge is a natural number and can be as large as six.

**Definition 1.8 (Rows realizing a profile).**

$$\forall k: Nat, (\forall p: \operatorname{Profile}\left(k\right), (\operatorname{Fiber}\left(p\right) = \{r: (\operatorname{Fin}\left(k + 1\right) \to \operatorname{Fin}\left(4\right)) \mid \forall j: \operatorname{Fin}\left(k\right), (\operatorname{edge}\left(r, j\right) = \operatorname{val}\left(p\left(j\right)\right))\}))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.Fiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The subtype fixes the natural sum at every edge to the corresponding profile entry.

**Definition 1.9 (Complementary profiles).**

$$\forall k: Nat, (\forall p: \operatorname{Profile}\left(k\right), (\forall j: \operatorname{Fin}\left(k\right), (\operatorname{flip}\left(p\right)\left(j\right) = \operatorname{Fin.rev}\left(p\left(j\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.flip` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reversal in Fin 3 sends each profile value s to 2−s at the same edge.

**Definition 1.10 (Row multiplicity).**

$$\forall k: Nat, (\forall p: \operatorname{Profile}\left(k\right), (\operatorname{b}\left(p\right) = \operatorname{Nat.card}\left(\operatorname{Fiber}\left(p\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.b` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural cardinality of the fiber counts individual rows with the prescribed edge sums.

**Definition 1.11 (Alternating row-profile count).**

$$\forall k: Nat, (\forall p: \operatorname{Profile}\left(k\right), (\forall h: Nat, (\operatorname{profileCount}\left(p, h\right) = \prod_{i: \operatorname{Fin}\left(h\right)} (\operatorname{b}\left(\operatorname{if}\left((\operatorname{val}\left(i\right) \bmod 2 = 0), p, \operatorname{flip}\left(p\right)\right)\right)))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.profileCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At an even row index choose the profile p, and at an odd index choose its complement. The three arguments of if give the condition, the even choice and the odd choice. The finite product is a natural number and the empty product is one.

**Lemma 1.12 (Adding two rows).**

$$\forall k: Nat, (\forall p: \operatorname{Profile}\left(k\right), (\forall h: Nat, (\operatorname{profileCount}\left(p, h + 2\right) = \operatorname{b}\left(p\right) \cdot \operatorname{b}\left(\operatorname{flip}\left(p\right)\right) \cdot \operatorname{profileCount}\left(p, h\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.profileCount_two_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adding two rows multiplies the natural count by the two complementary fiber sizes.

**Lemma 1.13 (Equal row multiplicities).**

$$\forall k: Nat, (\forall p: \operatorname{Profile}\left(k\right), (\forall c: Nat, ((\operatorname{b}\left(p\right) = c) \implies ((\operatorname{b}\left(\operatorname{flip}\left(p\right)\right) = c) \implies (\forall h: Nat, (\operatorname{profileCount}\left(p, h\right) = c^{h}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.profileCount_eq_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If both complementary fibers have the same size c, every row gives c choices.

**Lemma 1.14 (Profile sum for the rectangular count).**

$$\forall n: Nat, (\forall k: Nat, (\operatorname{T}\left(n + 1, k + 1\right) = \sum_{p: \operatorname{Profile}\left(k + 1\right)} (2 \cdot (\operatorname{profileCount}\left(p, n + 2\right): Int))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.literal_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are n+2 rows and k+2 columns here. The two uniform block-sum classes give the factor of two. Each natural alternating row-profile count is cast to an integer before the sum.

**Lemma 1.15 (Transposition of the literal count).**

$$\forall n: Nat, (\forall k: Nat, (\operatorname{T}\left(n, k\right) = \operatorname{T}\left(k, n\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.T_transpose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transposition swaps the grid dimensions and preserves the contiguous block condition. The count identity holds at all natural indices.

**Lemma 1.16 (The sum-two rectangular count).**

$$\forall n: Nat, (\forall k: Nat, (\operatorname{T}\left(n + 1, k + 1\right) = 2 \cdot (\operatorname{Nat.card}\left(\{A: \operatorname{Fin}\left(n + 1 + 1\right) \to \left(\operatorname{Fin}\left(k + 1 + 1\right) \to \operatorname{Fin}\left(4\right)\right) \mid \forall i: \operatorname{Fin}\left(n + 1\right), (\forall j: \operatorname{Fin}\left(k + 1\right), (\operatorname{Fin.val}\left(A\left(\operatorname{Fin.castSucc}\left(i\right), \operatorname{Fin.castSucc}\left(j\right)\right)\right) + \operatorname{Fin.val}\left(A\left(\operatorname{Fin.castSucc}\left(i\right), \operatorname{Fin.succ}\left(j\right)\right)\right) + \operatorname{Fin.val}\left(A\left(\operatorname{Fin.succ}\left(i\right), \operatorname{Fin.castSucc}\left(j\right)\right)\right) + \operatorname{Fin.val}\left(A\left(\operatorname{Fin.succ}\left(i\right), \operatorname{Fin.succ}\left(j\right)\right)\right) = 2))\}\right): \mathbb{Z})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.original_eq_twice_low` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The n+2 by k+2 arrays use the alphabet 0 through 3. The four entry values in every contiguous block sum to two in the naturals. The natural cardinality is cast to an integer before multiplication by two.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.Fiber`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.Grid`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.Legal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.Profile`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.T`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.T_transpose`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.b`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.edge`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.fin_constant`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.flip`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.literal_sum`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.original_eq_twice_low`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.profileCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.profileCount_eq_pow`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.profileCount_two_step`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.result`
