# Hardin's constant-stress alphabet comparisons

## Abstract

Hardin's literal constant-stress alphabet comparisons for A235280 and A235310.

## Source GID

`D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Alphabet`

**Definition 1.1 (Literal indexed count).**

$$\forall M: Nat, (\forall S: Nat, (\forall n: Nat, (\forall k: Nat, (\operatorname{C}\left(M, S, n, k\right) = \operatorname{Nat.card}\left(\{a: (\operatorname{Fin}\left(n + 1\right) \times \operatorname{Fin}\left(k + 1\right)) \to \operatorname{Fin}\left(M + 1\right) \mid \forall r: \operatorname{Fin}\left(n\right), (\forall c: \operatorname{Fin}\left(k\right), (\operatorname{Int.natAbs}\left(((\operatorname{val}\left(a\left((\operatorname{Fin.castSucc}\left(r\right), \operatorname{Fin.castSucc}\left(c\right))\right)\right): Int) + (\operatorname{val}\left(a\left((\operatorname{Fin.succ}\left(r\right), \operatorname{Fin.succ}\left(c\right))\right)\right): Int)) - ((\operatorname{val}\left(a\left((\operatorname{Fin.castSucc}\left(r\right), \operatorname{Fin.succ}\left(c\right))\right)\right): Int) + (\operatorname{val}\left(a\left((\operatorname{Fin.succ}\left(r\right), \operatorname{Fin.castSucc}\left(c\right))\right)\right): Int))\right) = S))\}\right)))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Alphabet.C` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinates are ordered. Each legal filling contributes once. The contiguous block condition tests the absolute difference of the two integer sums.

For positive n and k, a fixed deficit d, and M greater than d, checkerboard complementation sends stress 2M−d to block sums d and 4M−d. The gap is greater than the change possible across a shared edge, so the sum is uniform. Global complementation pairs the two classes. Every entry in the low class is at most d, and restricting the alphabet gives the exact count as twice the cardinality of the sum-d class over Fin (d+1).

**Definition 1.2 (Fixed-deficit equivalence).**

$$\forall M: Nat, (\forall d: Nat, (\forall n: Nat, (\forall k: Nat, ((d < M) \implies (\{a: \operatorname{Grid}\left(M, n + 1, k + 1\right) \mid \operatorname{Legal}\left(2 \cdot M - d, a\right)\} \equiv \operatorname{Sum}\left(\{a: \operatorname{Grid}\left(d, n + 1, k + 1\right) \mid \operatorname{Low}\left(d, a\right)\}, \{a: \operatorname{Grid}\left(d, n + 1, k + 1\right) \mid \operatorname{Low}\left(d, a\right)\}\right))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Alphabet.fixedDeficitEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here Grid(M,u,v) consists of functions from Fin (u+1) × Fin (v+1) to Fin (M+1). The successor indices u=n+1 and v=k+1 give n+2 rows and k+2 columns. Legal(S,a) is the absolute diagonal difference condition in every contiguous block. Low(d,a) requires the natural sum of its four entries to be d in every contiguous block. Sum denotes the tagged disjoint union.

Checkerboard complementation gives block sums d and 4M−d. The gap exceeds the change possible across a shared edge, so the sum is uniform. The first copy comes from the low class. Global complementation sends the high class to the low class for the second copy. Every entry in a low-class grid is at most d, so both copies use the alphabet 0 through d.

**Theorem 1.3 (A235280 alphabet comparison).**

$$\forall n: Nat, (\forall k: Nat, ((1 \le n) \implies ((1 \le k) \implies ((\operatorname{C}\left(4, 5, n, k\right) = \operatorname{C}\left(5, 7, n, k\right)) \land (\operatorname{C}\left(5, 7, n, k\right) = \operatorname{C}\left(6, 9, n, k\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Alphabet.a235280` (`✓ std3`). ∎

*Resolves.* `Problems/hardin-a235280-alphabet-comparison` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Alphabet.a235280`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin-a235280-alphabet-comparison","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Alphabet.a235280","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2014). *OEIS A235280 — Constant-stress rectangular arrays*. URL: <https://oeis.org/A235280>.

*Commentary.*

The common deficit is three. The NAME count is C(4, 5, n, k). The COMMENT specifies i = 1, 2, 3.

**Theorem 1.4 (A235310 alphabet comparison).**

$$\forall n: Nat, (\forall k: Nat, ((1 \le n) \implies ((1 \le k) \implies ((\operatorname{C}\left(5, 6, n, k\right) = \operatorname{C}\left(6, 8, n, k\right)) \land (\operatorname{C}\left(6, 8, n, k\right) = \operatorname{C}\left(7, 10, n, k\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Alphabet.a235310` (`✓ std3`). ∎

*Resolves.* `Problems/hardin-a235310-alphabet-comparison` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Alphabet.a235310`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin-a235310-alphabet-comparison","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Alphabet.a235310","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2014). *OEIS A235310 — Constant-stress rectangular arrays*. URL: <https://oeis.org/A235310>.

*Commentary.*

The common deficit is four. The NAME count is C(5, 6, n, k). The COMMENT specifies i = 1, 2, 3.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Alphabet.C`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Alphabet.a235280`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Alphabet.a235310`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Alphabet.fixedDeficitEquiv`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Alphabet](HardinA235289Alphabet.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence](HardinA235289Recurrence.md)
