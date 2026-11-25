# Hardin's constant-stress alphabet comparison

## Abstract

Hardin's alphabet comparison for literal constant-stress rectangles.

**Definition 1.1 (Literal count at alphabet parameter i).**

$$\forall n: Nat, (\forall k: Nat, (\forall i: Nat, (\operatorname{literalCount}\left(n, k, i\right) = (\operatorname{Nat.card}\left(\{A: \operatorname{Fin}\left(n + 1\right) \to \operatorname{Fin}\left(k + 1\right) \to \operatorname{Fin}\left(i + 3\right) \mid \forall r: \operatorname{Fin}\left(n\right), (\forall c: \operatorname{Fin}\left(k\right), (\operatorname{Int.natAbs}\left(((\operatorname{val}\left(A\left(\operatorname{Fin.castSucc}\left(r\right), \operatorname{Fin.castSucc}\left(c\right)\right)\right): Int) + (\operatorname{val}\left(A\left(\operatorname{Fin.succ}\left(r\right), \operatorname{Fin.succ}\left(c\right)\right)\right): Int)) - ((\operatorname{val}\left(A\left(\operatorname{Fin.castSucc}\left(r\right), \operatorname{Fin.succ}\left(c\right)\right)\right): Int) + (\operatorname{val}\left(A\left(\operatorname{Fin.succ}\left(r\right), \operatorname{Fin.castSucc}\left(c\right)\right)\right): Int))\right) = 2 + 2 \cdot i))\}\right): Int))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Alphabet.literalCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every indexed filling contributes once. Each pair of indices r and c selects the upper left corner of one contiguous block. Fin.castSucc preserves the index and Fin.succ increments it in the larger axis. The four entries are cast to integers before taking the difference of the diagonal and antidiagonal sums.

**Theorem 1.2 (Equality of the four literal counts).**

$$\forall n: Nat, (\forall k: Nat, (\forall i: Nat, ((1 \le n) \implies ((1 \le k) \implies ((i = 1 \lor i = 2 \lor i = 3 \lor i = 4) \implies (\operatorname{literalCount}\left(n, k, i\right) = \operatorname{T}\left(n, k\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Alphabet.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2014). *OEIS A235289 — Constant-stress rectangular arrays*. URL: <https://oeis.org/A235289>.

*Commentary.*

The integer count `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.T` uses the alphabet 0 through 3 and absolute diagonal difference four. Each filling of the indexed rectangle contributes once. The four choices of i give alphabet maxima 3, 4, 5, 6 and absolute differences 4, 6, 8, 10.

Write M = i+2 for the alphabet maximum. Replacing each entry x on one checkerboard color by M−x converts the block condition into a choice of sums 2 and 4M−2. Adjacent blocks share two cells, so their sums differ by at most 2M. For M at least 3 the two allowed sums differ by more than 2M. Every block sum therefore agrees with the sum in the corner block.

Complementing all entries exchanges the two classes. Every cell of a positive rectangle belongs to a block, so in the sum-two class every entry is 0, 1, or 2. Restricting the alphabet to these three entries and embedding it back are inverse. The count at each specified alphabet is twice the cardinality of this same class. The four-symbol baseline has that same count by its checkerboard and complement identity.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Alphabet.literalCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Alphabet.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.T`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence](HardinA235289Recurrence.md)
