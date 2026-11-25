# Strict Type I− exclusion

## Abstract

The strict Type I− hyperoctant excludes order-four unistochastic matrices.

**Definition 1.1 (Normalized Hadamard characters).**

$$H: \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(3\right), \mathbb{R}\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/Unistochastic/TypeIMinus.H` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ingemar Bengtsson, Åsa Ericsson, Marek Kuś, Wojciech Tadej, Karol Życzkowski (2004). *Birkhoff's polytope and unistochastic matrices, N = 3 and N = 4*. DOI: [10.1007/s00220-005-1392-8](https://doi.org/10.1007/s00220-005-1392-8). URL: <https://arxiv.org/abs/math/0402325v2>.

*Commentary.*

The four rows of H are (1,1,1), (1,−1,−1), (−1,1,−1), and (−1,−1,1), each divided by 2. The columns are orthonormal and perpendicular to the all-ones vector. Their outer products give the nine coordinates of the affine space of doubly stochastic matrices after centering.

**Theorem 1.2 (Every unitary has a nonnegative coordinate).**

$$\forall (U: \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \mathbb{C}\right)), U \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(4\right), \mathbb{C}\right) \to \exists (i j: \operatorname{Fin}\left(3\right)), 0 \le (\operatorname{Matrix.transpose}\left(H\right) \cdot \operatorname{RHLinalg.normSqMatrix}\left(U\right) \cdot H)\left(i, j\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/Unistochastic/TypeIMinus.exists_nonneg_typeIMinus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ingemar Bengtsson, Åsa Ericsson, Marek Kuś, Wojciech Tadej, Karol Życzkowski (2004). *Birkhoff's polytope and unistochastic matrices, N = 3 and N = 4*. DOI: [10.1007/s00220-005-1392-8](https://doi.org/10.1007/s00220-005-1392-8). URL: <https://arxiv.org/abs/math/0402325v2>.

*Commentary.*

The theorem answers Bengtsson, Ericsson, Kuś, Tadej, and Życzkowski's question in arXiv:math/0402325v2, §IV, p. 21. Their central-ray exclusion appears in §IV, pp. 19–20, using Appendix C. Row and column permutations preserve unitarity and permute the squared-norm matrix in the same way, so the exclusion also applies to the permutation images of this sector. The star-shapedness question for the full order-four unistochastic set in the same paragraph remains separate.

Assuming all nine coordinates are negative, choose a row whose products are bounded by the other rows' products on at least two column pairs. Hadamard sums give the off-diagonals of two planar overlap Gram matrices. The squared norms of the signed Hermitian unitary entries give the diagonal bounds and the exact difference between opposite row pairs. The two selected pairs force strictly larger Schur-complement diagonals and strictly smaller off-diagonal magnitude for the second Gram matrix. Both Schur complements have determinant zero, giving the contradiction.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/Unistochastic/TypeIMinus.H`
- Truth anchor: `D5/S3/Quantum/Matrix/Unistochastic/TypeIMinus.exists_nonneg_typeIMinus`
