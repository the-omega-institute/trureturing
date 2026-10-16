# Pairwise signs do not give an orthogonal lift at order five

## Abstract

The naive orthostochastic equations are insufficient at order five.

Indices belong to Fin n and start at zero. Every sum over Fin n includes all n indices. The source numbers indices from one. Signs are real numbers equal to 1 or −1. Allowing a sign on every term gives the same zero-sum condition as fixing the first sign to 1, since all signs may be reversed together. The Birkhoff polytope is Mathlib's doublyStochastic set.

**Definition 1.1 (Orthostochastic matrices).**

$$\forall (n: \mathbb{N}), \forall (B: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)), \operatorname{IsOrthostochastic}\left(B\right) = \exists (U: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)), (U \in \operatorname{Matrix.orthogonalGroup}\left(\operatorname{Fin}\left(n\right), \mathbb{R}\right)) \land (B = \operatorname{RHLinalg.normSqMatrix}\left(U\right))$$

*Formalization.* `D5/S3/Quantum/Matrix/ChenDeyNaiveEquationsFive.IsOrthostochastic` (`✓ std3`).

*Citation.* Justin Chen; Papri Dey (2023). *The 4 × 4 orthostochastic variety*. DOI: [10.1080/10586458.2021.1982427](https://doi.org/10.1080/10586458.2021.1982427). URL: <https://arxiv.org/abs/2001.10691>.

*Commentary.*

Section 1, page 1: "A real square matrix is called orthostochastic if it is the entrywise square of an orthogonal matrix." For real U, RHLinalg.normSqMatrix U has entry ‖U i j‖² = (U i j)².

**Definition 1.2 (The column naive equation).**

$$\forall (n: \mathbb{N}), \forall (B: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)), \forall (i: \operatorname{Fin}\left(n\right)), \forall (j: \operatorname{Fin}\left(n\right)), \operatorname{ColumnNaive}\left(B, i, j\right) = \exists (e: \operatorname{Fin}\left(n\right) \to \mathbb{R}), (\forall (k: \operatorname{Fin}\left(n\right)), (e\left(k\right) = 1) \lor (e\left(k\right) = -1)) \land (\sum_{k: \operatorname{Fin}\left(n\right)} e\left(k\right) \cdot \operatorname{Real.sqrt}\left(B\left(k, i\right) \cdot B\left(k, j\right)\right) = 0)$$

*Formalization.* `D5/S3/Quantum/Matrix/ChenDeyNaiveEquationsFive.ColumnNaive` (`✓ std3`).

*Citation.* Justin Chen; Papri Dey (2023). *The 4 × 4 orthostochastic variety*. DOI: [10.1080/10586458.2021.1982427](https://doi.org/10.1080/10586458.2021.1982427). URL: <https://arxiv.org/abs/2001.10691>.

*Commentary.*

After Definition 4, page 4: "a doubly stochastic matrix A satisfies C_{i,j} = 0 if and only if there exist choices of signs ε_1, …, ε_{n−1} such that with these choices of signs, the entrywise square roots of the i-th and j-th columns of A become orthogonal." The formula writes this sign condition; its application in claim assumes that the matrix is doubly stochastic.

**Definition 1.3 (The row naive equation).**

$$\forall (n: \mathbb{N}), \forall (B: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)), \forall (i: \operatorname{Fin}\left(n\right)), \forall (j: \operatorname{Fin}\left(n\right)), \operatorname{RowNaive}\left(B, i, j\right) = \exists (e: \operatorname{Fin}\left(n\right) \to \mathbb{R}), (\forall (k: \operatorname{Fin}\left(n\right)), (e\left(k\right) = 1) \lor (e\left(k\right) = -1)) \land (\sum_{k: \operatorname{Fin}\left(n\right)} e\left(k\right) \cdot \operatorname{Real.sqrt}\left(B\left(i, k\right) \cdot B\left(j, k\right)\right) = 0)$$

*Formalization.* `D5/S3/Quantum/Matrix/ChenDeyNaiveEquationsFive.RowNaive` (`✓ std3`).

*Citation.* Justin Chen; Papri Dey (2023). *The 4 × 4 orthostochastic variety*. DOI: [10.1080/10586458.2021.1982427](https://doi.org/10.1080/10586458.2021.1982427). URL: <https://arxiv.org/abs/2001.10691>.

*Commentary.*

Definition 4, page 3, defines the row equations "by transposing indices". RowNaive is the same sign condition with the row and column indices exchanged.

**Definition 1.4 (All row and column naive equations).**

$$\forall (n: \mathbb{N}), \forall (B: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)), \operatorname{SatisfiesNaive}\left(B\right) = \forall (i: \operatorname{Fin}\left(n\right)), \forall (j: \operatorname{Fin}\left(n\right)), (i < j) \Rightarrow ((\operatorname{ColumnNaive}\left(B, i, j\right)) \land (\operatorname{RowNaive}\left(B, i, j\right)))$$

*Formalization.* `D5/S3/Quantum/Matrix/ChenDeyNaiveEquationsFive.SatisfiesNaive` (`✓ std3`).

*Citation.* Justin Chen; Papri Dey (2023). *The 4 × 4 orthostochastic variety*. DOI: [10.1080/10586458.2021.1982427](https://doi.org/10.1080/10586458.2021.1982427). URL: <https://arxiv.org/abs/2001.10691>.

*Commentary.*

Definition 4, page 3, calls these the "naive equations" and counts n(n−1) equations in total. The formula requires both conditions for each i < j.

**Definition 1.5 (The positive five by five matrix).**

$$B = \operatorname{HSMul.hSMul}\left(\frac{1}{17}, (\operatorname{HSMul.hSMul}\left(4, \operatorname{Matrix.of}\left((1: \operatorname{Fin}\left(5\right) \to \operatorname{Fin}\left(5\right) \to \mathbb{R})\right)\right) - \operatorname{HSMul.hSMul}\left(3, (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(5\right), \operatorname{Fin}\left(5\right), \mathbb{R}\right))\right))\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/ChenDeyNaiveEquationsFive.B` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Justin Chen; Papri Dey (2023). *The 4 × 4 orthostochastic variety*. DOI: [10.1080/10586458.2021.1982427](https://doi.org/10.1080/10586458.2021.1982427). URL: <https://arxiv.org/abs/2001.10691>.

*Commentary.*

The matrix is (4J−3I)/17, with diagonal entries 1/17 and off-diagonal entries 4/17. The typed 1 supplied to Matrix.of is the constant function of two Fin 5 arguments with value 1, written fun _ _ => (1 : ℝ) in Lean. Every row and column sums to 1.

**Definition 1.6 (Question 5 at order five).**

$$claim = \forall (B: \operatorname{Matrix}\left(\operatorname{Fin}\left(5\right), \operatorname{Fin}\left(5\right), \mathbb{R}\right)), (B \in doublyStochastic\left(\mathbb{R}, \operatorname{Fin}\left(5\right)\right)) \Rightarrow ((\operatorname{SatisfiesNaive}\left(B\right)) \Rightarrow (\operatorname{IsOrthostochastic}\left(B\right)))$$

*Formalization.* `D5/S3/Quantum/Matrix/ChenDeyNaiveEquationsFive.claim` (`✓ std3`).

*Citation.* Justin Chen; Papri Dey (2023). *The 4 × 4 orthostochastic variety*. DOI: [10.1080/10586458.2021.1982427](https://doi.org/10.1080/10586458.2021.1982427). URL: <https://arxiv.org/abs/2001.10691>.

*Commentary.*

Question 5, page 4: "Do the naive equations define the orthostochastic variety inside B_n? In other words, if a doubly stochastic matrix satisfies C_{i,j}, R_{i,j} = 0 for all i < j, must it be orthostochastic?" Section 5, page 7: "Next, for n = 4, 5 it remains open whether the naive equations cut out the orthostochastic variety inside the Birkhoff polytope set-theoretically." The formula is the n = 5 clause: the matrix ranges over all real five by five matrices and the lift over all real orthogonal matrices.

**Theorem 1.7 (A negative answer at order five).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/ChenDeyNaiveEquationsFive.result` (`✓ std3`). ∎

*Resolves.* `Problems/chen-dey-2020-orthostochastic-naive-equations-five` (refuted) by `D5/S3/Quantum/Matrix/ChenDeyNaiveEquationsFive.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"chen-dey-2020-orthostochastic-naive-equations-five","declaration_gid":"D5/S3/Quantum/Matrix/ChenDeyNaiveEquationsFive.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Justin Chen; Papri Dey (2023). *The 4 × 4 orthostochastic variety*. DOI: [10.1080/10586458.2021.1982427](https://doi.org/10.1080/10586458.2021.1982427). URL: <https://arxiv.org/abs/2001.10691>.

*Commentary.*

For any two distinct columns of B, the five radical terms are 2/17, 2/17, 4/17, 4/17 and 4/17. Taking positive signs on the two distinguished positions and on one other position gives zero. Symmetry gives the row conditions. If B had a real orthogonal lift U, the matrix √17 U would have integer entries: ±1 on the diagonal and ±2 elsewhere. Its product with its transpose would be 17I, so its integer determinant would have square 17⁵. The latter is not a square. This answers the order-five clause negatively. The order-four clause remains open; the source's Proposition 6 already gives a negative answer for every n ≥ 6.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/ChenDeyNaiveEquationsFive.B`
- Truth anchor: `D5/S3/Quantum/Matrix/ChenDeyNaiveEquationsFive.ColumnNaive`
- Truth anchor: `D5/S3/Quantum/Matrix/ChenDeyNaiveEquationsFive.IsOrthostochastic`
- Truth anchor: `D5/S3/Quantum/Matrix/ChenDeyNaiveEquationsFive.RowNaive`
- Truth anchor: `D5/S3/Quantum/Matrix/ChenDeyNaiveEquationsFive.SatisfiesNaive`
- Truth anchor: `D5/S3/Quantum/Matrix/ChenDeyNaiveEquationsFive.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/ChenDeyNaiveEquationsFive.result`
