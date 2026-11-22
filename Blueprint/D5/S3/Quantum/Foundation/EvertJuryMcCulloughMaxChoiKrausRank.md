# Maximum Choi–Kraus rank of matrix products with units

## Abstract

The maximum Choi–Kraus rank is n³ for each of the left-unit and common-unit classes.

**Definition 1.1 (Square complex matrices).**

$$\forall (n: \mathbb{N}), (CMatrix\left(n\right) = Matrix\left(Fin\left(n\right), Fin\left(n\right), \mathbb{C}\right))$$

*Formalization.* `D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank.CMatrix` (`✓ std3`).

*Citation.* Eric Evert, Michael T. Jury and Scott McCullough (2026). *Completely Positive Matrix Products*. DOI: [10.48550/arXiv.2607.13251](https://doi.org/10.48550/arXiv.2607.13251). URL: <https://arxiv.org/pdf/2607.13251v1#page=22>.

*Commentary.*

The natural number n gives the common size of the row and column index sets.

**Definition 1.2 (Complex bilinear matrix products).**

$$\forall (n: \mathbb{N}), (\forall (m: \mathbb{N}), (MatrixProduct\left(n, m\right) = CMatrix\left(n\right) \Rightarrow_{\mathbb{C}} CMatrix\left(n\right) \Rightarrow_{\mathbb{C}} CMatrix\left(m\right)))$$

*Formalization.* `D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank.MatrixProduct` (`✓ std3`).

*Citation.* Eric Evert, Michael T. Jury and Scott McCullough (2026). *Completely Positive Matrix Products*. DOI: [10.48550/arXiv.2607.13251](https://doi.org/10.48550/arXiv.2607.13251). URL: <https://arxiv.org/pdf/2607.13251v1#page=22>.

*Commentary.*

Both inputs are n by n and the output is m by m. Each arrow in the displayed type is complex-linear.

**Definition 1.3 (An input block).**

$$\forall (n: \mathbb{N}), (\forall (ell: \mathbb{N}), (\forall (A: Matrix\left((Fin\left(ell\right) \times Fin\left(n\right)), (Fin\left(ell\right) \times Fin\left(n\right)), \mathbb{C}\right)), (\forall (i: Fin\left(ell\right)), (\forall (j: Fin\left(ell\right)), (\forall (a: Fin\left(n\right)), (\forall (b: Fin\left(n\right)), (block\left(A, i, j\right)\left(a, b\right) = A\left((i, a), (j, b)\right))))))))$$

*Formalization.* `D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank.block` (`✓ std3`).

*Citation.* Eric Evert, Michael T. Jury and Scott McCullough (2026). *Completely Positive Matrix Products*. DOI: [10.48550/arXiv.2607.13251](https://doi.org/10.48550/arXiv.2607.13251). URL: <https://arxiv.org/pdf/2607.13251v1#page=22>.

*Commentary.*

The block indices come first and the matrix indices come second.

**Definition 1.4 (Joint block amplification).**

$$\forall (n: \mathbb{N}), (\forall (m: \mathbb{N}), (\forall (\phi: MatrixProduct\left(n, m\right)), (\forall (ell: \mathbb{N}), (\forall (A: Matrix\left((Fin\left(ell\right) \times Fin\left(n\right)), (Fin\left(ell\right) \times Fin\left(n\right)), \mathbb{C}\right)), (\forall (B: Matrix\left((Fin\left(ell\right) \times Fin\left(n\right)), (Fin\left(ell\right) \times Fin\left(n\right)), \mathbb{C}\right)), (\forall (i: Fin\left(ell\right)), (\forall (j: Fin\left(ell\right)), (\forall (s: Fin\left(ell\right)), (\forall (t: Fin\left(ell\right)), (\forall (a: Fin\left(m\right)), (\forall (b: Fin\left(m\right)), (jointAmplification\left(\phi, A, B\right)\left(((i, s), a), ((j, t), b)\right) = \phi\left(block\left(A, i, j\right), block\left(B, s, t\right)\right)\left(a, b\right)))))))))))))$$

*Formalization.* `D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank.jointAmplification` (`✓ std3`).

*Citation.* Eric Evert, Michael T. Jury and Scott McCullough (2026). *Completely Positive Matrix Products*. DOI: [10.48550/arXiv.2607.13251](https://doi.org/10.48550/arXiv.2607.13251). URL: <https://arxiv.org/pdf/2607.13251v1#page=22>.

*Commentary.*

The two input blocks are evaluated independently. The output indices are ordered as a pair of block indices followed by a coordinate in the output matrix.

**Definition 1.5 (Joint complete positivity).**

$$\forall (n: \mathbb{N}), (\forall (m: \mathbb{N}), (\forall (\phi: MatrixProduct\left(n, m\right)), (IsJointlyCompletelyPositive\left(\phi\right) \iff (\forall (ell: \mathbb{N}), ((1 \le ell) \implies (\forall (A: Matrix\left((Fin\left(ell\right) \times Fin\left(n\right)), (Fin\left(ell\right) \times Fin\left(n\right)), \mathbb{C}\right)), (\forall (B: Matrix\left((Fin\left(ell\right) \times Fin\left(n\right)), (Fin\left(ell\right) \times Fin\left(n\right)), \mathbb{C}\right)), ((PosSemidef\left(A\right)) \implies ((PosSemidef\left(B\right)) \implies (PosSemidef\left(jointAmplification\left(\phi, A, B\right)\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank.IsJointlyCompletelyPositive` (`✓ std3`).

*Citation.* Eric Evert, Michael T. Jury and Scott McCullough (2026). *Completely Positive Matrix Products*. DOI: [10.48550/arXiv.2607.13251](https://doi.org/10.48550/arXiv.2607.13251). URL: <https://arxiv.org/pdf/2607.13251v1#page=22>.

*Commentary.*

Equation (2.1) requires positivity on two positive semidefinite block matrices at every positive block size.

**Definition 1.6 (Kraus representations of length N).**

$$\forall (n: \mathbb{N}), (\forall (m: \mathbb{N}), (\forall (\phi: MatrixProduct\left(n, m\right)), (\forall (N: \mathbb{N}), (HasKrausRepresentation\left(\phi, N\right) \iff (\exists (V: Fin\left(N\right) \to Matrix\left((Fin\left(n\right) \times Fin\left(n\right)), Fin\left(m\right), \mathbb{C}\right)), (\forall (A: CMatrix\left(n\right)), (\forall (B: CMatrix\left(n\right)), (\phi\left(A, B\right) = \sum_{k \in Fin\left(N\right)} V\left(k\right)^{*} kronecker\left(A, B\right) V\left(k\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank.HasKrausRepresentation` (`✓ std3`).

*Citation.* Eric Evert, Michael T. Jury and Scott McCullough (2026). *Completely Positive Matrix Products*. DOI: [10.48550/arXiv.2607.13251](https://doi.org/10.48550/arXiv.2607.13251). URL: <https://arxiv.org/pdf/2607.13251v1#page=22>.

*Commentary.*

Theorem 2.1 uses n² by m coefficients and the conjugate transpose on the left. The length zero gives an empty sum.

**Definition 1.7 (Minimum Kraus length).**

$$\forall (n: \mathbb{N}), (\forall (m: \mathbb{N}), (\forall (\phi: MatrixProduct\left(n, m\right)), (choiKrausRank\left(\phi\right) = sInf\left(\{(r: \mathbb{N}_{\infty}) \mid \exists (N: \mathbb{N}), ((r = (N: \mathbb{N}_{\infty})) \land (HasKrausRepresentation\left(\phi, N\right)))\}\right))))$$

*Formalization.* `D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank.choiKrausRank` (`✓ std3`).

*Citation.* Eric Evert, Michael T. Jury and Scott McCullough (2026). *Completely Positive Matrix Products*. DOI: [10.48550/arXiv.2607.13251](https://doi.org/10.48550/arXiv.2607.13251). URL: <https://arxiv.org/pdf/2607.13251v1#page=22>.

*Commentary.*

Remark 2.2 defines the rank by the minimum length. The infimum is taken in the extended natural numbers, so an empty set of admissible lengths has value infinity.

**Definition 1.8 (Choi matrix in input-input-output order).**

$$\forall (n: \mathbb{N}), (\forall (m: \mathbb{N}), (\forall (\phi: MatrixProduct\left(n, m\right)), (\forall (i: Fin\left(n\right)), (\forall (j: Fin\left(n\right)), (\forall (s: Fin\left(n\right)), (\forall (t: Fin\left(n\right)), (\forall (a: Fin\left(m\right)), (\forall (b: Fin\left(m\right)), (choiMatrix\left(\phi\right)\left(((i, s), a), ((j, t), b)\right) = \phi\left(E_{(i, j)}, E_{(s, t)}\right)\left(a, b\right))))))))))$$

*Formalization.* `D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank.choiMatrix` (`✓ std3`).

*Citation.* Eric Evert, Michael T. Jury and Scott McCullough (2026). *Completely Positive Matrix Products*. DOI: [10.48550/arXiv.2607.13251](https://doi.org/10.48550/arXiv.2607.13251). URL: <https://arxiv.org/pdf/2607.13251v1#page=22>.

*Commentary.*

The explicit tensor sum in Theorem 2.1 uses E(i,j) and E(s,t) as n by n matrix units. Swapping both input positions in the nested block convention preserves rank and positivity.

**Definition 1.9 (Left unit).**

$$\forall (n: \mathbb{N}), (\forall (\phi: MatrixProduct\left(n, n\right)), (\forall (L: CMatrix\left(n\right)), (IsLeftUnit\left(\phi, L\right) \iff (\forall (Y: CMatrix\left(n\right)), (\phi\left(L, Y\right) = Y)))))$$

*Formalization.* `D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank.IsLeftUnit` (`✓ std3`).

*Citation.* Eric Evert, Michael T. Jury and Scott McCullough (2026). *Completely Positive Matrix Products*. DOI: [10.48550/arXiv.2607.13251](https://doi.org/10.48550/arXiv.2607.13251). URL: <https://arxiv.org/pdf/2607.13251v1#page=22>.

*Commentary.*

Section 5.3 requires the left identity at every complex matrix Y. L ranges over all complex matrices.

**Definition 1.10 (Right unit).**

$$\forall (n: \mathbb{N}), (\forall (\phi: MatrixProduct\left(n, n\right)), (\forall (R: CMatrix\left(n\right)), (IsRightUnit\left(\phi, R\right) \iff (\forall (X: CMatrix\left(n\right)), (\phi\left(X, R\right) = X)))))$$

*Formalization.* `D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank.IsRightUnit` (`✓ std3`).

*Citation.* Eric Evert, Michael T. Jury and Scott McCullough (2026). *Completely Positive Matrix Products*. DOI: [10.48550/arXiv.2607.13251](https://doi.org/10.48550/arXiv.2607.13251). URL: <https://arxiv.org/pdf/2607.13251v1#page=22>.

*Commentary.*

Section 5.3 requires the right identity at every complex matrix X.

**Definition 1.11 (Common two-sided unit).**

$$\forall (n: \mathbb{N}), (\forall (\phi: MatrixProduct\left(n, n\right)), (\forall (T: CMatrix\left(n\right)), (IsUnit\left(\phi, T\right) \iff ((IsLeftUnit\left(\phi, T\right)) \land (IsRightUnit\left(\phi, T\right))))))$$

*Formalization.* `D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank.IsUnit` (`✓ std3`).

*Citation.* Eric Evert, Michael T. Jury and Scott McCullough (2026). *Completely Positive Matrix Products*. DOI: [10.48550/arXiv.2607.13251](https://doi.org/10.48550/arXiv.2607.13251). URL: <https://arxiv.org/pdf/2607.13251v1#page=22>.

*Commentary.*

The same complex matrix T supplies both identities.

**Definition 1.12 (The two clauses of Question 1).**

$$claim \iff (\forall (n: \mathbb{N}), ((1 \le n) \implies (((\forall (\phi: MatrixProduct\left(n, n\right)), ((IsJointlyCompletelyPositive\left(\phi\right)) \implies ((\exists (L: CMatrix\left(n\right)), (IsLeftUnit\left(\phi, L\right))) \implies (choiKrausRank\left(\phi\right) \le (n^{3}: \mathbb{N}_{\infty}))))) \land (\exists (\phi: MatrixProduct\left(n, n\right)), ((IsJointlyCompletelyPositive\left(\phi\right)) \land ((\exists (L: CMatrix\left(n\right)), (IsLeftUnit\left(\phi, L\right))) \land (choiKrausRank\left(\phi\right) = (n^{3}: \mathbb{N}_{\infty})))))) \land ((\forall (\phi: MatrixProduct\left(n, n\right)), ((IsJointlyCompletelyPositive\left(\phi\right)) \implies ((\exists (T: CMatrix\left(n\right)), (IsUnit\left(\phi, T\right))) \implies (choiKrausRank\left(\phi\right) \le (n^{3}: \mathbb{N}_{\infty}))))) \land (\exists (\phi: MatrixProduct\left(n, n\right)), ((IsJointlyCompletelyPositive\left(\phi\right)) \land ((\exists (T: CMatrix\left(n\right)), (IsUnit\left(\phi, T\right))) \land (choiKrausRank\left(\phi\right) = (n^{3}: \mathbb{N}_{\infty})))))))))$$

*Formalization.* `D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eric Evert, Michael T. Jury and Scott McCullough (2026). *Completely Positive Matrix Products*. DOI: [10.48550/arXiv.2607.13251](https://doi.org/10.48550/arXiv.2607.13251). URL: <https://arxiv.org/pdf/2607.13251v1#page=22>.

*Commentary.*

Question 1 in Section 5.3, printed page 22, asks “What is the maximum Choi-Kraus rank of a jcp product with a left unit?” and “What is the maximum Choi-Kraus rank of a jcp product with a unit?” For every n ≥ 1, Lean considers complex bilinear products with both inputs and the output of size n and requires joint complete positivity at every positive block size on every pair of positive semidefinite block inputs. The first class requires a left unit, and the second requires one matrix satisfying both unit identities. The units range over all complex n by n matrices. For each class, the extended-natural infimum of Kraus lengths is at most n³ for every qualifying product and equals n³ for some qualifying product.

**Theorem 1.13 (The two sharp maxima).**

$$\forall (n: \mathbb{N}), ((1 \le n) \implies (((\forall (\phi: MatrixProduct\left(n, n\right)), ((IsJointlyCompletelyPositive\left(\phi\right)) \implies ((\exists (L: CMatrix\left(n\right)), (IsLeftUnit\left(\phi, L\right))) \implies (choiKrausRank\left(\phi\right) \le (n^{3}: \mathbb{N}_{\infty}))))) \land (\exists (\phi: MatrixProduct\left(n, n\right)), ((IsJointlyCompletelyPositive\left(\phi\right)) \land ((\exists (L: CMatrix\left(n\right)), (IsLeftUnit\left(\phi, L\right))) \land (choiKrausRank\left(\phi\right) = (n^{3}: \mathbb{N}_{\infty})))))) \land ((\forall (\phi: MatrixProduct\left(n, n\right)), ((IsJointlyCompletelyPositive\left(\phi\right)) \implies ((\exists (T: CMatrix\left(n\right)), (IsUnit\left(\phi, T\right))) \implies (choiKrausRank\left(\phi\right) \le (n^{3}: \mathbb{N}_{\infty}))))) \land (\exists (\phi: MatrixProduct\left(n, n\right)), ((IsJointlyCompletelyPositive\left(\phi\right)) \land ((\exists (T: CMatrix\left(n\right)), (IsUnit\left(\phi, T\right))) \land (choiKrausRank\left(\phi\right) = (n^{3}: \mathbb{N}_{\infty}))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank.result` (`✓ std3`). ∎

*Resolves.* `Problems/evert-jury-mccullough-2026-max-choi-kraus-rank` (proved) by `D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"evert-jury-mccullough-2026-max-choi-kraus-rank","declaration_gid":"D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Eric Evert, Michael T. Jury and Scott McCullough (2026). *Completely Positive Matrix Products*. DOI: [10.48550/arXiv.2607.13251](https://doi.org/10.48550/arXiv.2607.13251). URL: <https://arxiv.org/pdf/2607.13251v1#page=22>.

*Commentary.*

Test joint block positivity at size n on two copies of the matrix-unit block matrix given by the unnormalized maximally entangled dyad. The result is the Choi matrix. Simultaneously permute row and column indices to use the output-first Choi convention for a linear map. Its action on simple Kronecker tensors is the original bilinear map, by their values on matrix units and bilinearity.

The positive semidefinite Choi matrix gives a rectangular Kraus family indexed by the n³ Choi coordinates. Conversely, each Kraus coefficient acts by a sandwich on a permutation of the tensor product of the two block inputs, yielding positivity at every block size. Flattening the coefficients expresses the Choi matrix as a sum of N outer products, so its rank is at most N. If the Choi matrix is positive definite, this forces every admissible length to be at least n³.

For n at least two let J be the all-ones matrix and I the identity. The weighted Schur product with weights I + J has common unit T = J − I/2. With H = (2n − 1)I − J, add the product of the two functionals A ↦ Tr(HA) and B ↦ Tr(HB), times I. The functional vanishes at T, and H is positive definite. The added Choi matrix is the tensor product of the two transposes of H and I. It is positive definite, and the weighted Schur contribution is positive semidefinite.

At n = 1 ordinary scalar multiplication has unit 1 and positive-definite Choi matrix. In every dimension the common-unit example also attains the left-unit maximum. The upper bound applies to all jointly completely positive square products, independently of their units. For n at least two the attaining unit is indefinite.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank.CMatrix`
- Truth anchor: `D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank.HasKrausRepresentation`
- Truth anchor: `D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank.IsJointlyCompletelyPositive`
- Truth anchor: `D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank.IsLeftUnit`
- Truth anchor: `D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank.IsRightUnit`
- Truth anchor: `D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank.IsUnit`
- Truth anchor: `D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank.MatrixProduct`
- Truth anchor: `D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank.block`
- Truth anchor: `D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank.choiKrausRank`
- Truth anchor: `D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank.choiMatrix`
- Truth anchor: `D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank.claim`
- Truth anchor: `D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank.jointAmplification`
- Truth anchor: `D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank.result`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](FiniteKrausRepresentation.md)
