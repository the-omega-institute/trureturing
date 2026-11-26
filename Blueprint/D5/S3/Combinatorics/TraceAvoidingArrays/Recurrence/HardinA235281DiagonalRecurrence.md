# Hardin's constant-stress square arrays

## Abstract

The seven-lag recurrence for Hardin's square arrays.

**Theorem 1.1 (The seven-lag diagonal recurrence).**

$$\forall m: Nat, ((1 \le m) \implies (\operatorname{T}\left(m + 7, m + 7\right) = \operatorname{T}\left(m + 6, m + 6\right) + 9 \cdot \operatorname{T}\left(m + 5, m + 5\right) - 9 \cdot \operatorname{T}\left(m + 4, m + 4\right) - 26 \cdot \operatorname{T}\left(m + 3, m + 3\right) + 26 \cdot \operatorname{T}\left(m + 2, m + 2\right) + 24 \cdot \operatorname{T}\left(m + 1, m + 1\right) - 24 \cdot \operatorname{T}\left(m, m\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235281DiagonalRecurrence.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin-a235281-diagonal-recurrence` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235281DiagonalRecurrence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin-a235281-diagonal-recurrence","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235281DiagonalRecurrence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2014). *OEIS A235281 — Constant-stress square arrays*. URL: <https://oeis.org/A235281>.

*Commentary.*

OEIS A235281 counts literal square fillings by 0 through 3 whose contiguous two-by-two blocks have absolute diagonal difference four. Its term at index m is the rectangular count T(m,m) of A235289, for a square of side m+1. The offset is one, so the displayed recurrence first computes term eight. The index arithmetic is natural and the signed count identity is over the integers.

The rectangular profile sum counts each uniform block-sum-two filling twice to account for the two classes under complementation. Within the sum, a row with a prescribed profile is determined by any one cell. At an edge with sum s there are at most s+1 choices for its first cell. Thus the multiplicities of a profile and its complement add to at most three if the profile takes two different values. When both multiplicities are positive they are (1,1), (1,2) or (2,1). The three constant profiles have multiplicities 1, 2 and 3, obtained by alternating two entries with the prescribed sum.

Write n+2 for the number of rows and k+2 for the number of columns. Let w(a,d,h) be the product of h alternating factors a,d,a,d,… beginning with a. Set U(n) = 2^(n+2) + w(1,3,n+2) + w(3,1,n+2) and V(n) = w(1,2,n+2) + w(2,1,n+2). The constant profiles contribute U(n). Write C(k) for the number of nonconstant profiles with pair (1,1) and D(k) for those with pair (1,2). Complementation pairs the (1,2) and (2,1) profiles, giving T(n+1,k+1) = 2(U(n) + C(k) + D(k)V(n)).

Width two has only constant profiles. Transposing the width-two arrays and using V(0) = 4 eliminates C(k). Transposing against width three, where V(1) = 6, gives 2D(k) = D(1)(V(k) − 4). On the diagonal these identities give T(n+1,n+1) = 4U(n) − 2U(0) + D(1)(V(n) − 4)^2.

Under a two-index shift the power of two in U is multiplied by four, the other part of U by three, V by two, and V squared by four. After expanding the square, the constant contribution is killed by E−1, where E shifts the index by one. The full diagonal is therefore annihilated by (E−1)(E^2−2)(E^2−3)(E^2−4). Expanding this polynomial gives the displayed coefficients.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235281DiagonalRecurrence.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence](HardinA235289Recurrence.md)
