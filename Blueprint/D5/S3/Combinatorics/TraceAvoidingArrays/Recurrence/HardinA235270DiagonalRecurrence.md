# The A235270 diagonal recurrence

## Abstract

Hardin's eleven-lag recurrence for indexed constant-stress squares.

**Theorem 1.1 (The A235270 eleven-lag recurrence).**

$$\begin{aligned}&\forall n: \mathbb{N}, 1 \le n \implies\\(\operatorname{C}\left(4, 5, n + 11, n + 11\right) : \mathbb{Z}) &=(\operatorname{C}\left(4, 5, n + 10, n + 10\right) : \mathbb{Z})+23\cdot(\operatorname{C}\left(4, 5, n + 9, n + 9\right) : \mathbb{Z})-23\cdot(\operatorname{C}\left(4, 5, n + 8, n + 8\right) : \mathbb{Z})\\&\quad-200\cdot(\operatorname{C}\left(4, 5, n + 7, n + 7\right) : \mathbb{Z})+200\cdot(\operatorname{C}\left(4, 5, n + 6, n + 6\right) : \mathbb{Z})+820\cdot(\operatorname{C}\left(4, 5, n + 5, n + 5\right) : \mathbb{Z})\\&\quad-820\cdot(\operatorname{C}\left(4, 5, n + 4, n + 4\right) : \mathbb{Z})-1584\cdot(\operatorname{C}\left(4, 5, n + 3, n + 3\right) : \mathbb{Z})+1584\cdot(\operatorname{C}\left(4, 5, n + 2, n + 2\right) : \mathbb{Z})\\&\quad+1152\cdot(\operatorname{C}\left(4, 5, n + 1, n + 1\right) : \mathbb{Z})-1152\cdot(\operatorname{C}\left(4, 5, n, n\right) : \mathbb{Z})\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235270DiagonalRecurrence.a235270_order11` (`✓ std3`). ∎

*Resolves.* `Problems/hardin-a235270-diagonal-recurrence` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235270DiagonalRecurrence.a235270_order11`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin-a235270-diagonal-recurrence","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235270DiagonalRecurrence.a235270_order11","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2014). *OEIS A235270 — Constant-stress square arrays*. URL: <https://oeis.org/A235270>.

*Commentary.*

The integer cast of C(4,5,n,n) counts indexed square arrays of side n+1 over entries 0 through 4. Every contiguous 2×2 block has absolute difference 5 between its diagonal and antidiagonal sums. Each lag shifts both sides of the square. The first full window uses indices 1 through 12.

For a row with a prescribed horizontal edge-sum profile, a forward shift raises the even-column entries and lowers the odd-column entries. The minimum odd-column entry counts the forward steps available. Counting pairs from complementary profiles with prescribed numbers of available steps reduces to independent column choices. Mixed second differences give the exact frequencies of the two fiber sizes.

The profile expansion on the square diagonal has constant terms, zero terms and terms multiplied by 2, 3, 4, 6 or 8 under a two-index advance. The polynomial (X−1)(X²−2)(X²−3)(X²−4)(X²−6)(X²−8) annihilates the sum for the forward shift X. Its expansion gives the signed recurrence.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235270DiagonalRecurrence.a235270_order11`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Recurrence](HardinA235280A235310Recurrence.md)
