# Invertibility of Cartesian-control angle matrices

## Abstract

The real angle matrix of a finite Cartesian control set is invertible for every pair of enumerations and every choice of coordinate dimensions.

**Definition 1.1 (The angle matrix for two enumerations).**

$$\forall \left(k: \mathbb{N}\right), \left(\forall \left(d: \left(\operatorname{Fin}\left(k\right)\right) \to \left(\mathbb{N}\right)\right), \left(\forall \left(b: \operatorname{Equiv}\left(\operatorname{Fin}\left(\prod_{l: \operatorname{Fin}\left(k\right)} \left(d\left(l\right)\right)\right), \left(\left(l: \operatorname{Fin}\left(k\right)\right) \to \operatorname{Fin}\left(d\left(l\right)\right)\right)\right)\right), \left(\forall \left(g: \operatorname{Equiv}\left(\operatorname{Fin}\left(\prod_{l: \operatorname{Fin}\left(k\right)} \left(d\left(l\right)\right)\right), \left(\left(l: \operatorname{Fin}\left(k\right)\right) \to \operatorname{Fin}\left(d\left(l\right)\right)\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Matrix.CartesianControlAngleMatrixInvertible.angleMatrix}\left(d, b, g\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(\prod_{l: \operatorname{Fin}\left(k\right)} \left(d\left(l\right)\right)\right), \operatorname{Fin}\left(\prod_{l: \operatorname{Fin}\left(k\right)} \left(d\left(l\right)\right)\right), \mathbb{R}\right)\right) = \left(\lambda \left(i: \operatorname{Fin}\left(\prod_{l: \operatorname{Fin}\left(k\right)} \left(d\left(l\right)\right)\right)\right) \mapsto \left(\lambda \left(j: \operatorname{Fin}\left(\prod_{l: \operatorname{Fin}\left(k\right)} \left(d\left(l\right)\right)\right)\right) \mapsto \left(\prod_{l: \operatorname{Fin}\left(k\right)} \left(\operatorname{ite}\left(\left(\left(\left(0: \mathbb{N}\right) < \left(\operatorname{Fin.val}\left(\operatorname{Equiv.toFun}\left(b, i, l\right)\right): \mathbb{N}\right)\right) \land \left(\left(\operatorname{Fin.val}\left(\operatorname{Equiv.toFun}\left(b, i, l\right)\right): \mathbb{N}\right) \le \left(\operatorname{Fin.val}\left(\operatorname{Equiv.toFun}\left(g, j, l\right)\right): \mathbb{N}\right)\right)\right), -\left(1: \mathbb{R}\right), \left(1: \mathbb{R}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/CartesianControlAngleMatrixInvertible.angleMatrix` (`✓ std3`).

*Citation.* Jacky Jiang; Natalie Klco; Olivia Di Matteo (2025). *Non-Abelian dynamics on a cube: Improving quantum compilation through qudit-based simulations*. DOI: [10.1103/rrmd-fqx6](https://doi.org/10.1103/rrmd-fqx6). URL: <https://arxiv.org/abs/2506.10945v1>.

*Commentary.*

A control word chooses a digit in Fin (d l) at every coordinate l in Fin k. The equivalences b and g enumerate all such words by Fin of the product of the dimensions. For row i and column j, each coordinate contributes minus one exactly when the natural digit of b i is positive and is at most the corresponding natural digit of g j; otherwise it contributes one. The matrix entry is the product of these real signs. Equiv.toFun makes the use of an equivalence as a function explicit, and Fin.val converts each digit to a natural number. This is the matrix of equation (5), subsec_3a_uniform-rotations.tex, lines 38–49, with arbitrary coordinate dimensions and arbitrary enumerations, as used for the two sequences in subsec_3c_restricted-rotations.tex, lines 34–36.

**Definition 1.2 (Invertibility for every finite Cartesian product).**

$$\left(\operatorname{D5.S3.Quantum.Matrix.CartesianControlAngleMatrixInvertible.claim}\right) \Leftrightarrow \left(\forall \left(k: \mathbb{N}\right), \left(\forall \left(d: \left(\operatorname{Fin}\left(k\right)\right) \to \left(\mathbb{N}\right)\right), \left(\forall \left(b: \operatorname{Equiv}\left(\operatorname{Fin}\left(\prod_{l: \operatorname{Fin}\left(k\right)} \left(d\left(l\right)\right)\right), \left(\left(l: \operatorname{Fin}\left(k\right)\right) \to \operatorname{Fin}\left(d\left(l\right)\right)\right)\right)\right), \left(\forall \left(g: \operatorname{Equiv}\left(\operatorname{Fin}\left(\prod_{l: \operatorname{Fin}\left(k\right)} \left(d\left(l\right)\right)\right), \left(\left(l: \operatorname{Fin}\left(k\right)\right) \to \operatorname{Fin}\left(d\left(l\right)\right)\right)\right)\right), \left(\operatorname{IsUnit}\left(\operatorname{D5.S3.Quantum.Matrix.CartesianControlAngleMatrixInvertible.angleMatrix}\left(d, b, g\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/CartesianControlAngleMatrixInvertible.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jacky Jiang; Natalie Klco; Olivia Di Matteo (2025). *Non-Abelian dynamics on a cube: Improving quantum compilation through qudit-based simulations*. DOI: [10.1103/rrmd-fqx6](https://doi.org/10.1103/rrmd-fqx6). URL: <https://arxiv.org/abs/2506.10945v1>.

*Commentary.*

For every natural k, every family d of natural dimensions, and every pair of equivalences b and g enumerating the Cartesian product, the angle matrix is a unit in the real square-matrix ring. Thus it has a two-sided matrix inverse. The conjecture in subsec_3c_restricted-rotations.tex, lines 38–46, concerns the sequences produced by the source's particular construction. The assertion here applies to every pair of enumerations. It includes dimensions zero and one and the empty family of coordinates, without a positivity assumption. The sequencing algorithms of app_3c_sequencers.tex, lines 31–40, are not part of this assertion.

**Theorem 1.3 (The angle matrix is invertible).**

$$\forall \left(k: \mathbb{N}\right), \left(\forall \left(d: \left(\operatorname{Fin}\left(k\right)\right) \to \left(\mathbb{N}\right)\right), \left(\forall \left(b: \operatorname{Equiv}\left(\operatorname{Fin}\left(\prod_{l: \operatorname{Fin}\left(k\right)} \left(d\left(l\right)\right)\right), \left(\left(l: \operatorname{Fin}\left(k\right)\right) \to \operatorname{Fin}\left(d\left(l\right)\right)\right)\right)\right), \left(\forall \left(g: \operatorname{Equiv}\left(\operatorname{Fin}\left(\prod_{l: \operatorname{Fin}\left(k\right)} \left(d\left(l\right)\right)\right), \left(\left(l: \operatorname{Fin}\left(k\right)\right) \to \operatorname{Fin}\left(d\left(l\right)\right)\right)\right)\right), \left(\operatorname{IsUnit}\left(\operatorname{D5.S3.Quantum.Matrix.CartesianControlAngleMatrixInvertible.angleMatrix}\left(d, b, g\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CartesianControlAngleMatrixInvertible.result` (`✓ std3`). ∎

*Resolves.* `Problems/jiang-klco-di-matteo-2025-cartesian-control-angle-matrix-invertibility` (proved) by `D5/S3/Quantum/Matrix/CartesianControlAngleMatrixInvertible.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"jiang-klco-di-matteo-2025-cartesian-control-angle-matrix-invertibility","declaration_gid":"D5/S3/Quantum/Matrix/CartesianControlAngleMatrixInvertible.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jacky Jiang; Natalie Klco; Olivia Di Matteo (2025). *Non-Abelian dynamics on a cube: Improving quantum compilation through qudit-based simulations*. DOI: [10.1103/rrmd-fqx6](https://doi.org/10.1103/rrmd-fqx6). URL: <https://arxiv.org/abs/2506.10945v1>.

*Commentary.*

First consider the real square matrix on Fin m whose entry at r,s is minus one when 0 < r ≤ s and one otherwise, using the natural values of the indices. Multiply it on the left by the row transformation that keeps row zero and replaces every positive row r by half of row zero minus half of row r. The resulting entry at r,s is one when r ≤ s and zero otherwise: row zero consists of ones, and for positive r the difference is one exactly when r ≤ s. This is the zeta matrix of the linearly ordered set Fin m.

The zeta matrix is upper triangular and has every diagonal entry equal to one, so its determinant is one. Taking determinants of the preceding product shows that the determinant of the row transformation times the determinant of the sign matrix is one. The latter determinant is therefore a unit. These determinant identities include m equal to zero, where the diagonal product is empty.

Next index rows and columns by control words and form the product matrix whose entry at r,s is the product, over l, of the one-coordinate sign-matrix entries at r l,s l. Form a second matrix by taking the same coordinatewise product of the inverses of those sign matrices. To multiply the second matrix by the first, sum over the intermediate control word r. Distribute the products inside that sum and factor the sum over all words into the product of the sums over each individual digit. Each such sum is an entry of the corresponding one-coordinate inverse times its original matrix, hence is one when the two endpoint digits agree and zero otherwise. The product is one exactly when all endpoint digits agree. Function extensionality identifies this condition with equality of the endpoint words, so the second matrix is a left inverse of the product matrix.

A square matrix with a left inverse has unit determinant, and a square matrix whose determinant is a unit is itself a unit. Finally, the angle matrix is the submatrix of this product matrix obtained by reindexing its rows through b and its columns through g. Both maps are equivalences, so this independent reindexing preserves being a unit. This proves the assertion for all k,d,b,g, including empty index types and empty products.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/CartesianControlAngleMatrixInvertible.angleMatrix`
- Truth anchor: `D5/S3/Quantum/Matrix/CartesianControlAngleMatrixInvertible.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/CartesianControlAngleMatrixInvertible.result`
