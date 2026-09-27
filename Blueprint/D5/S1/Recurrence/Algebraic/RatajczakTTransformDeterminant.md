# Ratajczak's A110491 T-Transform Determinant

## Abstract

Ratajczak's literal T-transform determinant equals the independently specified A110491 sequence in every positive matrix order.

Natural sequence indices start at zero, while matrix row and column indices in the source start at one. For a zero-based finite index, i1=val(i)+1 and j1=val(j)+1 implement that conversion. The lower branch remains literally sourceB(2*j1); it is not simplified to one inside the matrix definition. Matrix entries and determinants are integers. The sourceA sequence is specified independently by its two initial values and order-two recurrence, not by a determinant.

**Definition 1.1 (The A093178 source sequence).**

$$\forall r: \mathbb{N}, \operatorname{sourceB}\left(r\right) = \operatorname{ite}\left(\operatorname{Even}\left(r\right), 1, (r: \mathbb{Z})\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/RatajczakTTransformDeterminant.sourceB` (`✓ std3`).

*Citation.* Lechoslaw Ratajczak (2021). *OEIS A110491, T-transform determinant conjecture for A093178*. URL: <https://oeis.org/A110491>.

*Commentary.*

The source sequence is one at even indices and is the index itself at odd indices. Although only positive arguments occur in the source matrix, the declaration is total on the natural numbers.

**Definition 1.2 (The independent A110491 recurrence).**

$$\begin{aligned}\operatorname{sourceA}\left(0\right) = 1\\\operatorname{sourceA}\left(1\right) = 2\\\forall m: \mathbb{N}, \operatorname{sourceA}\left(m + 2\right) = 2 \cdot \operatorname{sourceA}\left(m + 1\right) + 4 \cdot (m + 1: \mathbb{Z}) \cdot (m: \mathbb{Z}) \cdot \operatorname{sourceA}\left(m\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Algebraic/RatajczakTTransformDeterminant.sourceA` (`✓ std3`).

*Citation.* Lechoslaw Ratajczak (2021). *OEIS A110491, T-transform determinant conjecture for A093178*. URL: <https://oeis.org/A110491>.

*Commentary.*

The target sequence starts with 1 and 2. Its next value is twice the preceding value plus 4(m+1)m times the value two positions back. This recurrence fixes every integer value independently of the matrix.

**Definition 1.3 (The literal T-transform matrix).**

$$\forall n: \mathbb{N}, \forall i: \operatorname{Fin}\left(n\right), \forall j: \operatorname{Fin}\left(n\right), \operatorname{sourceMatrix}\left(n, i, j\right) = \operatorname{ite}\left(\operatorname{val}\left(i\right) + 1 > \operatorname{val}\left(j\right) + 1, \operatorname{sourceB}\left(2 \cdot \left(\operatorname{val}\left(j\right) + 1\right)\right), \operatorname{sourceB}\left(\operatorname{val}\left(i\right) + 1 + \operatorname{val}\left(j\right) + 1 - 1\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/RatajczakTTransformDeterminant.sourceMatrix` (`✓ std3`).

*Citation.* Lechoslaw Ratajczak (2021). *OEIS A110491, T-transform determinant conjecture for A093178*. URL: <https://oeis.org/A110491>.

*Commentary.*

The finite matrix uses the source's one-based i and j. Strictly below the diagonal its entry is sourceB(2*j1); on and above the diagonal its entry is sourceB(i1+j1-1). Thus the formal object retains both the source indexing and the stated lower branch exactly.

**Theorem 1.4 (The all-order determinant identity).**

$$\forall m: \mathbb{N}, \operatorname{det}\left(\operatorname{sourceMatrix}\left(m + 1\right)\right) = \operatorname{sourceA}\left(m\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/RatajczakTTransformDeterminant.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a110491-ratajczak-t-transform-determinant` (proved) by `D5/S1/Recurrence/Algebraic/RatajczakTTransformDeterminant.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a110491-ratajczak-t-transform-determinant","declaration_gid":"D5/S1/Recurrence/Algebraic/RatajczakTTransformDeterminant.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Lechoslaw Ratajczak (2021). *OEIS A110491, T-transform determinant conjecture for A093178*. URL: <https://oeis.org/A110491>.

*Commentary.*

Subtracting each predecessor row leaves a leading one and reduces the determinant to the m-by-m matrix H. Conjugation by the alternating-sign diagonal extracts the factor 2^m and leaves the floor-linear matrix L. Subtracting each adjacent predecessor column from its successor converts L to the parity-upper matrix B. Multiplication by U2, the identity minus the second-superdiagonal matrix, has determinant one and converts B to the signed tridiagonal matrix T with diagonal one, subdiagonal p and superdiagonal -p. Reversing its indices and expanding the sparse front gives d_(m+2)=d_(m+1)+(m+1)m d_m. After restoring 2^m this is exactly the sourceA recurrence. The empty and one-dimensional determinants supply the m=0 and m=1 base cases, so the equality holds for every natural m, equivalently every positive matrix order m+1.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/RatajczakTTransformDeterminant.result`
- Truth anchor: `D5/S1/Recurrence/Algebraic/RatajczakTTransformDeterminant.sourceA`
- Truth anchor: `D5/S1/Recurrence/Algebraic/RatajczakTTransformDeterminant.sourceB`
- Truth anchor: `D5/S1/Recurrence/Algebraic/RatajczakTTransformDeterminant.sourceMatrix`
