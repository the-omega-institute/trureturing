# Clue geometry of four by four SudoQ

## Abstract

Clue-fixing isometries force a repeated ray in every SudoQ unit.

Vectors belong to EuclideanSpace over Complex with four coordinates. Rows and columns use zero-based Fin indices. A clue fixes its literal vector; equality of solutions compares each entry up to a unit complex phase. Four orthonormal vectors in this space form an orthonormal basis.

**Definition 1.1 (Block coordinates).**

$$\forall b \in \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right),\; \forall k \in \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right),\; \operatorname{blockCell}\left(b, k\right) = (\operatorname{finProdFinEquiv}\left((b.1, k.1)\right), \operatorname{finProdFinEquiv}\left((b.2, k.2)\right))$$

*Formalization.* `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.blockCell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For block b and offset k, the cell has coordinates 2*b.1+k.1 and 2*b.2+k.2. Each coordinate uses Mathlib's finProdFinEquiv on the corresponding block index and offset.

**Definition 1.2 (SudoQ constraints).**

$$\forall G \in \operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(4\right) \to \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right)\right),\; \operatorname{IsSudoQ}\left(G\right) = \left(\left(\forall i \in \operatorname{Fin}\left(4\right),\; \operatorname{Orthonormal}\left(\mathbb{C}, fun (j: \operatorname{Fin}\left(4\right)) \mapsto G (i, j)\right)\right) \land \left(\left(\forall j \in \operatorname{Fin}\left(4\right),\; \operatorname{Orthonormal}\left(\mathbb{C}, fun (i: \operatorname{Fin}\left(4\right)) \mapsto G (i, j)\right)\right) \land \left(\forall b \in \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right),\; \operatorname{Orthonormal}\left(\mathbb{C}, fun (k: \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \mapsto G (\operatorname{blockCell}\left(b, k\right).1, \operatorname{blockCell}\left(b, k\right).2)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.IsSudoQ` (`✓ std3`).

*Citation.* J. Paczos, M. Wierzbiński, G. Rajchel-Mieldzioć, A. Burchardt, K. Życzkowski (2021). *Genuinely quantum SudoQ and its cardinality*. DOI: [10.1103/PhysRevA.104.042423](https://doi.org/10.1103/PhysRevA.104.042423). URL: <https://arxiv.org/abs/2106.02967v2>.

*Commentary.*

Definition 7, page 3: “A quantum Sudoku (SudoQ) is an $N^{2} \times N^{2}$ QLS with additional constraints that each of the disjoint blocks of size $N$ forms an orthonormal basis.” Definition 2, page 2: “A quantum Latin square (QLS) is an $N \times N$ array of vectors from $N$-dimensional Hilbert space $\mathcal{H}_{N}$, arranged in such a way that each row and column forms an orthonormal basis of $\mathcal{H}_{N}$.” Here the Sudoku parameter is N=2, and the Latin square dimension is four. All four rows, four columns and four disjoint blocks are quantified.

**Definition 1.3 (A completion with prescribed clues).**

$$\forall C \in \operatorname{Finset}\left(\operatorname{Fin}\left(4\right) \times \operatorname{Fin}\left(4\right)\right),\; \forall v \in \operatorname{Fin}\left(4\right) \times \operatorname{Fin}\left(4\right) \to \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right),\; \forall G \in \operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(4\right) \to \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right)\right),\; \operatorname{IsSolution}\left(C, v, G\right) = \left(\operatorname{IsSudoQ}\left(G\right) \land \left(\forall c \in \operatorname{Fin}\left(4\right) \times \operatorname{Fin}\left(4\right),\; c \in C \Rightarrow G (c.1, c.2) = v (c)\right)\right)$$

*Formalization.* `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.IsSolution` (`✓ std3`).

*Citation.* J. Paczos, M. Wierzbiński, G. Rajchel-Mieldzioć, A. Burchardt, K. Życzkowski (2021). *Genuinely quantum SudoQ and its cardinality*. DOI: [10.1103/PhysRevA.104.042423](https://doi.org/10.1103/PhysRevA.104.042423). URL: <https://arxiv.org/abs/2106.02967v2>.

*Commentary.*

Definition 8, page 3: “A quantum grid is a SudoQ grid whose some entries can be blank.” Definition 9, page 3: “A quantum grid is called solvable if it has at least one solution.” C is precisely the set of nonblank cells, as in the six-clue example after Definition 9. v prescribes their vectors, and G is a completion. Values of v outside C are unrestricted.

**Definition 1.4 (Entrywise equality as rays).**

$$\forall G \in \operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(4\right) \to \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right)\right),\; \forall H \in \operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(4\right) \to \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right)\right),\; \operatorname{SameRays}\left(G, H\right) = \left(\forall i \in \operatorname{Fin}\left(4\right),\; \forall j \in \operatorname{Fin}\left(4\right),\; \exists z \in \mathbb{C},\; \Vert z \Vert = 1 \land H (i, j) = z \cdot G (i, j)\right)$$

*Formalization.* `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.SameRays` (`✓ std3`).

*Citation.* J. Paczos, M. Wierzbiński, G. Rajchel-Mieldzioć, A. Burchardt, K. Życzkowski (2021). *Genuinely quantum SudoQ and its cardinality*. DOI: [10.1103/PhysRevA.104.042423](https://doi.org/10.1103/PhysRevA.104.042423). URL: <https://arxiv.org/abs/2106.02967v2>.

*Commentary.*

Definition 5, page 2: “The cardinality c of a QLS is the number of its vectors distinct up to a global phase.” Each entry may have its own unit phase z. This is the ray convention used when comparing solutions.

**Definition 1.5 (Unique solvability).**

$$\forall C \in \operatorname{Finset}\left(\operatorname{Fin}\left(4\right) \times \operatorname{Fin}\left(4\right)\right),\; \forall v \in \operatorname{Fin}\left(4\right) \times \operatorname{Fin}\left(4\right) \to \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right),\; \operatorname{UniquelySolvable}\left(C, v\right) = \left(\exists G \in \operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(4\right) \to \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right)\right),\; \operatorname{IsSolution}\left(C, v, G\right) \land \left(\forall H \in \operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(4\right) \to \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right)\right),\; \operatorname{IsSolution}\left(C, v, H\right) \Rightarrow \operatorname{SameRays}\left(G, H\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.UniquelySolvable` (`✓ std3`).

*Citation.* J. Paczos, M. Wierzbiński, G. Rajchel-Mieldzioć, A. Burchardt, K. Życzkowski (2021). *Genuinely quantum SudoQ and its cardinality*. DOI: [10.1103/PhysRevA.104.042423](https://doi.org/10.1103/PhysRevA.104.042423). URL: <https://arxiv.org/abs/2106.02967v2>.

*Commentary.*

Definition 10, page 3: “A quantum grid is called uniquely solvable if it has a unique solution.” The existential quantifier requires a completion; every other completion agrees with it as rays. It does not require literal equality of phase representatives.

**Definition 1.6 (Two vectors on the same normalized ray).**

$$\forall x \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right),\; \forall y \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right),\; \operatorname{RayEq}\left(x, y\right) = \left(\exists z \in \mathbb{C},\; \Vert z \Vert = 1 \land y = z \cdot x\right)$$

*Formalization.* `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.RayEq` (`✓ std3`).

*Citation.* J. Paczos, M. Wierzbiński, G. Rajchel-Mieldzioć, A. Burchardt, K. Życzkowski (2021). *Genuinely quantum SudoQ and its cardinality*. DOI: [10.1103/PhysRevA.104.042423](https://doi.org/10.1103/PhysRevA.104.042423). URL: <https://arxiv.org/abs/2106.02967v2>.

*Commentary.*

Definition 5, page 2: “The cardinality c of a QLS is the number of its vectors distinct up to a global phase.” RayEq makes the unit-phase relation explicit for a single pair of vectors.

**Definition 1.7 (A ray occurring once in every unit).**

$$\forall G \in \operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(4\right) \to \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right)\right),\; \forall w \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right),\; \operatorname{HasRepeatedRay}\left(G, w\right) = \left(\left(\forall i \in \operatorname{Fin}\left(4\right),\; \exists! (j: \operatorname{Fin}\left(4\right)), \operatorname{RayEq}\left(w, G (i, j)\right)\right) \land \left(\left(\forall j \in \operatorname{Fin}\left(4\right),\; \exists! (i: \operatorname{Fin}\left(4\right)), \operatorname{RayEq}\left(w, G (i, j)\right)\right) \land \left(\forall b \in \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right),\; \exists! (k: \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \operatorname{RayEq}\left(w, G (\operatorname{blockCell}\left(b, k\right).1, \operatorname{blockCell}\left(b, k\right).2)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.HasRepeatedRay` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ray of w occurs exactly once in every row, column and block. The uniqueness quantifiers range over all four positions of each unit.

**Theorem 1.8 (Symmetry of ray equality).**

$$\forall x \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right),\; \forall y \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right),\; \operatorname{RayEq}\left(x, y\right) \Rightarrow \operatorname{RayEq}\left(y, x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Inverting the unit phase reverses ray equality.

**Theorem 1.9 (Transitivity of ray equality).**

$$\forall x \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right),\; \forall y \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right),\; \forall z \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right),\; \operatorname{RayEq}\left(x, y\right) \Rightarrow \left(\operatorname{RayEq}\left(y, z\right) \Rightarrow \operatorname{RayEq}\left(x, z\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.trans` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying the unit phases composes ray equality.

**Theorem 1.10 (A scalar between unit vectors is a unit phase).**

$$\forall x \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right),\; \forall y \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right),\; \Vert x \Vert = 1 \Rightarrow \left(\Vert y \Vert = 1 \Rightarrow \left(\left(\exists z \in \mathbb{C},\; y = z \cdot x\right) \Rightarrow \operatorname{RayEq}\left(x, y\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.rayEq_of_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of the norms forces the scalar to have norm one.

**Theorem 1.11 (An orthogonal vector is a different ray).**

$$\forall x \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right),\; \forall y \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right),\; \Vert x \Vert = 1 \Rightarrow \left(\operatorname{inner}\left(\mathbb{C}, x, y\right) = 0 \Rightarrow \left(\neg \operatorname{RayEq}\left(x, y\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.not_rayEq_of_orthogonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A unit vector cannot be orthogonal to a unit-phase multiple of itself.

**Theorem 1.12 (Reflexivity of ray equality).**

$$\forall x \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right),\; \operatorname{RayEq}\left(x, x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.refl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The phase one fixes every vector.

**Theorem 1.13 (Ray equality preserves norm).**

$$\forall x \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right),\; \forall y \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right),\; \operatorname{RayEq}\left(x, y\right) \Rightarrow \Vert y \Vert = \Vert x \Vert$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication by a unit complex phase preserves norm.

**Theorem 1.14 (Orthogonality is unchanged in the left ray).**

$$\forall x \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right),\; \forall u \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right),\; \forall y \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right),\; \operatorname{RayEq}\left(x, u\right) \Rightarrow \left(\operatorname{inner}\left(\mathbb{C}, u, y\right) = 0 \Leftrightarrow \operatorname{inner}\left(\mathbb{C}, x, y\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.inner_left_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugate linearity and the nonzero unit phase preserve a zero inner product.

**Theorem 1.15 (Orthogonality is unchanged in the right ray).**

$$\forall x \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right),\; \forall y \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right),\; \forall u \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right),\; \operatorname{RayEq}\left(y, u\right) \Rightarrow \left(\operatorname{inner}\left(\mathbb{C}, x, u\right) = 0 \Leftrightarrow \operatorname{inner}\left(\mathbb{C}, x, y\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.inner_right_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Linearity and the nonzero unit phase preserve a zero inner product.

**Theorem 1.16 (Unique solvability would force a repeated ray).**

$$\forall C \in \operatorname{Finset}\left(\operatorname{Fin}\left(4\right) \times \operatorname{Fin}\left(4\right)\right),\; \forall v \in \operatorname{Fin}\left(4\right) \times \operatorname{Fin}\left(4\right) \to \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right),\; \forall G \in \operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(4\right) \to \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right)\right),\; \operatorname{Finset}.\operatorname{card} (C) \le 3 \Rightarrow \left(\operatorname{IsSolution}\left(C, v, G\right) \Rightarrow \left(\left(\forall H \in \operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(4\right) \to \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right)\right),\; \operatorname{IsSolution}\left(C, v, H\right) \Rightarrow \operatorname{SameRays}\left(G, H\right)\right) \Rightarrow \left(\exists w \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right),\; \Vert w \Vert = 1 \land \operatorname{HasRepeatedRay}\left(G, w\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.unique_implies_repeated_ray` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be the complex span of the clue vectors. At most three clues make S a proper subspace. Reflection in S fixes the clues. If all solutions agree as rays, each entry lies in S or its orthogonal complement. Swapping two orthogonal basis vectors in that complement also fixes the clues and changes a ray, so the complement must be one-dimensional. Its unit ray then occurs exactly once in every orthonormal row, column and block.

## References

- Truth anchor: `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.HasRepeatedRay`
- Truth anchor: `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.IsSolution`
- Truth anchor: `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.IsSudoQ`
- Truth anchor: `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.RayEq`
- Truth anchor: `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.SameRays`
- Truth anchor: `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.UniquelySolvable`
- Truth anchor: `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.blockCell`
- Truth anchor: `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.inner_left_iff`
- Truth anchor: `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.inner_right_iff`
- Truth anchor: `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.norm`
- Truth anchor: `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.not_rayEq_of_orthogonal`
- Truth anchor: `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.rayEq_of_smul`
- Truth anchor: `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.refl`
- Truth anchor: `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.symm`
- Truth anchor: `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.trans`
- Truth anchor: `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.unique_implies_repeated_ray`
