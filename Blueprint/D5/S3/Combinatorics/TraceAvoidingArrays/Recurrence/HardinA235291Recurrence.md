# The A235291 two-column recurrence

## Abstract

Hardin's signed order-four recurrence for indexed two-column arrays.

**Theorem 1.1 (The A235291 signed recurrence).**

$$\forall n: \mathbb{N}, 5 \le n \implies \operatorname{a}\left(n\right) = 14 \cdot \operatorname{a}\left(n - 2\right) - 48 \cdot \operatorname{a}\left(n - 4\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235291Recurrence.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin-a235291-two-column-recurrence` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235291Recurrence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin-a235291-two-column-recurrence","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235291Recurrence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2014). *OEIS A235291 — Constant-stress two-column arrays*. URL: <https://oeis.org/A235291>.

*Commentary.*

Let a(n) be the integer cast of C(3,3,n,1), the number of indexed (n+1)-by-2 arrays with entries 0 through 3. Each contiguous 2-by-2 block has absolute difference 3 between the diagonal and antidiagonal sums. The first complete recurrence window ends at index 5.

A row with signed difference d between its entries has 4−|d| possible fillings. Two rows may be adjacent exactly when their differences d differ by 3 in absolute value. The transfer sums over admissible next differences, with the number of fillings as the weight of each.

One step makes the function values at differences −3 and 3 equal, since both lead only to 0. On functions with that equality, two steps multiply the component {−3,0,3} by 8 and each of {−2,1} and {−1,2} by 6. Thus (X²−6)(X²−8) annihilates the transfer after the first step, for arbitrary terminal weights. Taking unit terminal weights and summing over first rows gives the signed recurrence for the number of arrays.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235291Recurrence.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Alphabet](HardinA235280A235310Alphabet.md)
