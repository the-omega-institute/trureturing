# Hardin's constant-stress rectangular arrays

## Abstract

Hardin's common six-lag recurrence for constant-stress rectangular arrays.

**Definition 1.1 (Rectangular arrays).**

$$\forall n: Nat, (\forall k: Nat, (\operatorname{Grid}\left(n, k\right) = \operatorname{Fin}\left(n + 1\right) \to \operatorname{Fin}\left(k + 1\right) \to \operatorname{Fin}\left(4\right)))$$

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

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2014). *OEIS A235289 — Constant-stress rectangular arrays*. URL: <https://oeis.org/A235289>.

*Commentary.*

OEIS A235289 proposes a common recurrence for every row and every column. The pair d gives the row and column indices of the table. Either varying index starts at seven, since the smallest lagged index in each displayed identity is positive.

Complementing every cell on one checkerboard color converts the diagonal difference into a block sum of two or ten. Adjacent blocks share two cells. Their sums can differ by at most six, so every block has the same sum. Complementing all cells exchanges the two classes.

For a sum-two array, the horizontal adjacent sums in successive rows alternate between a profile and its complement in two. Each profile and its complement have at most four row choices in total, since the first cell determines a row from its adjacent sums. The nonzero contributions have one-step multiplier one or two, or two-step multiplier two or three. Each contribution satisfies the displayed recurrence, and summing the contributions proves the first identity. Transposition gives the second.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.Grid`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.Legal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.T`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.result`
