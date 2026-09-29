# Cyclic Latin Eulerian Numbers Are Not Fully Symmetric

## Abstract

The column-ascent counts of cyclic Latin squares change only when an endpoint symbol wraps, which refutes full permutation symmetry of the ascent vector.

**Definition 1.1 (Row-reordered cyclic square).**

$$\forall n \in \mathrm{Nat},\; \forall pi \in \operatorname{EquivPerm}\left(\operatorname{Fin}\left(n\right)\right),\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall c \in \operatorname{Fin}\left(n\right),\; \operatorname{cyclicSquare}\left(n, pi, i, c\right) = \operatorname{pi}\left(i\right) + c$$

*Formalization.* `D5/S3/Combinatorics/CyclicLatinEulerianRefutation.cyclicSquare` (`✓ std3`).

*Citation.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Cyclic Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.28808](https://doi.org/10.48550/arXiv.2609.28808). URL: <https://arxiv.org/abs/2609.28808v1>.

*Commentary.*

The entry in row i and column c is the value of the row permutation at i, shifted by c in Fin n.

**Definition 1.2 (Cyclic Latin Eulerian number).**

$$\forall n \in \mathrm{Nat},\; \forall k \in \operatorname{Fin}\left(n\right) \to \mathrm{Nat},\; \operatorname{cyclicLatinEulerian}\left(n, k\right) = \operatorname{card}\left(\{ pi \in \operatorname{EquivPerm}\left(\operatorname{Fin}\left(n\right)\right) | \forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{colAscents}\left(n, \operatorname{cyclicSquare}\left(n, pi\right), j\right) = \operatorname{k}\left(j\right)\} \right)$$

*Formalization.* `D5/S3/Combinatorics/CyclicLatinEulerianRefutation.cyclicLatinEulerian` (`✓ std3`).

*Citation.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Cyclic Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.28808](https://doi.org/10.48550/arXiv.2609.28808). URL: <https://arxiv.org/abs/2609.28808v1>.

*Commentary.*

Count the row permutations whose column-ascent vector equals k at every column. Column ascents are counted from the first row to the last.

**Definition 1.3 (Full permutation symmetry).**

$$claim \Leftrightarrow \left(\forall n \in \mathrm{Nat},\; \forall k \in \operatorname{Fin}\left(n\right) \to \mathrm{Nat},\; \forall sigma \in \operatorname{EquivPerm}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{cyclicLatinEulerian}\left(n, k \circ sigma\right) = \operatorname{cyclicLatinEulerian}\left(n, k\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/CyclicLatinEulerianRefutation.claim` (`✓ std3`).

*Citation.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Cyclic Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.28808](https://doi.org/10.48550/arXiv.2609.28808). URL: <https://arxiv.org/abs/2609.28808v1>.

*Commentary.*

The asserted equality compares the count for k with the count for k after any permutation of its column coordinates, at every order.

**Theorem 1.4 (One-column shift identity).**

$$\forall n \in \mathrm{Nat},\; \forall pi \in \operatorname{EquivPerm}\left(\operatorname{Fin}\left(n\right)\right),\; \forall c \in \operatorname{Fin}\left(n\right),\; 2 \le n \Rightarrow \operatorname{colAscents}\left(n, \operatorname{cyclicSquare}\left(n, pi\right), c + \operatorname{fin}\left(1, n\right)\right) + \operatorname{if}\left(\operatorname{val}\left(\operatorname{pi}\left(\operatorname{fin}\left(n - 1, n\right)\right) + c\right) = n - 1, 1, 0\right) = \operatorname{colAscents}\left(n, \operatorname{cyclicSquare}\left(n, pi\right), c\right) + \operatorname{if}\left(\operatorname{val}\left(\operatorname{pi}\left(\operatorname{fin}\left(0, n\right)\right) + c\right) = n - 1, 1, 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicLatinEulerianRefutation.shift_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Cyclic Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.28808](https://doi.org/10.48550/arXiv.2609.28808). URL: <https://arxiv.org/abs/2609.28808v1>.

*Commentary.*

For order at least two, shifting the column by one changes its ascent count only through the wrapping symbol in the first and last rows. The endpoint indicators balance the two column counts.

**Theorem 1.5 (Three consecutive shifts cannot all change).**

$$\forall n \in \mathrm{Nat},\; \forall pi \in \operatorname{EquivPerm}\left(\operatorname{Fin}\left(n\right)\right),\; 4 \le n \Rightarrow \left(\operatorname{colAscents}\left(n, \operatorname{cyclicSquare}\left(n, pi\right), \operatorname{fin}\left(0, n\right)\right) = \operatorname{colAscents}\left(n, \operatorname{cyclicSquare}\left(n, pi\right), \operatorname{fin}\left(1, n\right)\right) \lor \left(\operatorname{colAscents}\left(n, \operatorname{cyclicSquare}\left(n, pi\right), \operatorname{fin}\left(1, n\right)\right) = \operatorname{colAscents}\left(n, \operatorname{cyclicSquare}\left(n, pi\right), \operatorname{fin}\left(2, n\right)\right) \lor \operatorname{colAscents}\left(n, \operatorname{cyclicSquare}\left(n, pi\right), \operatorname{fin}\left(2, n\right)\right) = \operatorname{colAscents}\left(n, \operatorname{cyclicSquare}\left(n, pi\right), \operatorname{fin}\left(3, n\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicLatinEulerianRefutation.no_three_changes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Cyclic Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.28808](https://doi.org/10.48550/arXiv.2609.28808). URL: <https://arxiv.org/abs/2609.28808v1>.

*Commentary.*

At order at least four, among the first three successive column pairs, at least one pair has equal ascent counts. Distinct wrapping symbols cannot all occupy the two endpoint rows.

**Theorem 1.6 (Failure at every order at least four).**

$$\forall n \in \mathrm{Nat},\; 4 \le n \Rightarrow \left(\exists k \in \operatorname{Fin}\left(n\right) \to \mathrm{Nat},\; \exists sigma \in \operatorname{EquivPerm}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{cyclicLatinEulerian}\left(n, k \circ sigma\right) \ne \operatorname{cyclicLatinEulerian}\left(n, k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicLatinEulerianRefutation.not_fully_symmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Cyclic Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.28808](https://doi.org/10.48550/arXiv.2609.28808). URL: <https://arxiv.org/abs/2609.28808v1>.

*Commentary.*

Exchange the last two values of the identity row permutation, then exchange the second and third coordinates of its ascent vector. The original vector is attained, while the exchanged vector would require three consecutive changes and is unattained.

**Theorem 1.7 (Full symmetry is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicLatinEulerianRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/mirzavaziri-yaqubi-cyclic-full-symmetry-refutation` (refuted) by `D5/S3/Combinatorics/CyclicLatinEulerianRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mirzavaziri-yaqubi-cyclic-full-symmetry-refutation","declaration_gid":"D5/S3/Combinatorics/CyclicLatinEulerianRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Cyclic Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.28808](https://doi.org/10.48550/arXiv.2609.28808). URL: <https://arxiv.org/abs/2609.28808v1>.

*Commentary.*

The asserted equality fails already at order four, and the preceding construction supplies a failure at every larger order.

## References

- Truth anchor: `D5/S3/Combinatorics/CyclicLatinEulerianRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/CyclicLatinEulerianRefutation.cyclicLatinEulerian`
- Truth anchor: `D5/S3/Combinatorics/CyclicLatinEulerianRefutation.cyclicSquare`
- Truth anchor: `D5/S3/Combinatorics/CyclicLatinEulerianRefutation.no_three_changes`
- Truth anchor: `D5/S3/Combinatorics/CyclicLatinEulerianRefutation.not_fully_symmetric`
- Truth anchor: `D5/S3/Combinatorics/CyclicLatinEulerianRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/CyclicLatinEulerianRefutation.shift_step`
- Dependency: [D5/S3/Combinatorics/LatinEulerianDefs](LatinEulerianDefs.md)
