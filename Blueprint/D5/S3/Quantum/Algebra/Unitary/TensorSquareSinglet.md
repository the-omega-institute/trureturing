# Invariant subspaces of the tensor square of two qubits

## Abstract

For every set of two-by-two complex matrices containing two explicit special unitary matrices, the subspaces of the two-qubit space invariant under every tensor square g tensor g with g in the set are exactly zero, the singlet line, its orthogonal complement of symmetric tensors, which has dimension three, and the whole space; every g tensor g multiplies the singlet by det g.

V denotes the Euclidean space of complex functions on Fin(2) x Fin(2), the two-qubit space with orthonormal basis |00>, |01>, |10>, |11>; x_{ij} is the coordinate of x at |ij>. For a two-by-two complex matrix g, kron(g, g) is the Kronecker product of g with itself, acting on V as the matrix of g tensor g in this basis.

**Definition 1.1 (The singlet).**

$$V = \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)\right),\quad\\\omega \in V,\quad\omega_{01} = 1,\quad\omega_{10} = -1,\quad\omega_{00} = 0,\quad\omega_{11} = 0.$$

*Formalization.* `D5/S3/Quantum/Algebra/Unitary/TensorSquareSinglet.singlet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The singlet omega is the unnormalized vector |01> - |10> of V: its coordinate at |01> is 1, at |10> it is -1, and the other two coordinates are 0.

**Definition 1.2 (The diagonal phase matrix).**

$$\operatorname{phaseMatrix} = \begin{pmatrix} \frac{3 + 4i}{5} & 0 \\ 0 & \frac{3 - 4i}{5} \end{pmatrix}$$

*Formalization.* `D5/S3/Quantum/Algebra/Unitary/TensorSquareSinglet.phaseMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

phaseMatrix is the diagonal matrix with diagonal entries (3 + 4i)/5 and (3 - 4i)/5, two complex numbers of modulus one with product one.

**Definition 1.3 (The real rotation matrix).**

$$\operatorname{rotationMatrix} = \begin{pmatrix} \frac{3}{5} & -\frac{4}{5} \\ \frac{4}{5} & \frac{3}{5} \end{pmatrix}$$

*Formalization.* `D5/S3/Quantum/Algebra/Unitary/TensorSquareSinglet.rotationMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

rotationMatrix is the rotation of the plane with cosine 3/5 and sine 4/5, viewed as a complex matrix.

**Theorem 1.4 (Invariant subspaces of the tensor square).**

$$V = \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)\right),\quad\\\operatorname{phaseMatrix} \in \operatorname{specialUnitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right) \land \operatorname{rotationMatrix} \in \operatorname{specialUnitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right) \land\\(\forall S \in \operatorname{Set}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right),\; \operatorname{phaseMatrix} \in S \Rightarrow \left(\operatorname{rotationMatrix} \in S \Rightarrow \left(\forall W \in \operatorname{Submodule}\left(\mathbb{C}, V\right),\; \left(\forall g \in S,\; \forall x \in W,\; \operatorname{kron}\left(g, g\right)\left(x\right) \in W\right) \Leftrightarrow \left(W = 0 \lor \left(W = \mathbb{C} \omega \lor \left(W = (\mathbb{C} \omega)^{\perp} \lor W = V\right)\right)\right)\right)\right)) \land\\(\forall g \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{kron}\left(g, g\right)\left(\omega\right) = \operatorname{det}\left(g\right) \omega) \land\\(\forall x \in V,\; x \in (\mathbb{C} \omega)^{\perp} \Leftrightarrow x_{01} = x_{10}) \land \operatorname{finrank}\left(\mathbb{C}, (\mathbb{C} \omega)^{\perp}\right) = 3$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Unitary/TensorSquareSinglet.singlet_invariant_subspaces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the display, specialUnitaryGroup(Fin(2), C) is the group of two-by-two unitary matrices of determinant one, Set(M) is the type of sets of two-by-two complex matrices, Submodule(C, V) is the type of complex subspaces of V, 0 is the zero subspace, C omega is the line spanned by omega, and the last term V of the four-fold disjunction is the whole space. The theorem has six conjuncts. phaseMatrix and rotationMatrix are special unitary. For every set S of two-by-two complex matrices containing both, a subspace W of V is invariant under kron(g, g) for every g in S if and only if W is 0, the line of omega, its orthogonal complement, or V. For every two-by-two complex matrix g, kron(g, g) sends omega to det(g) omega. A vector lies in the orthogonal complement of omega exactly when its coordinates at |01> and |10> agree. The orthogonal complement has dimension three. Taking S to be the special unitary group gives the invariant subspaces under all of SU(2); the same statement covers the general linear group and the set consisting of the two matrices alone.

In coordinates (a, b, c, d) at |00>, |01>, |10>, |11>, the coordinates of kron(g, g) applied to omega are 0, g_{00} g_{11} - g_{01} g_{10}, its negative, and 0, which gives det(g) omega for every matrix g, unitary or not; the symmetric tensors b = c are mapped to symmetric tensors by the same computation. So all four subspaces are invariant under every kron(g, g). Conversely, kron(phaseMatrix, phaseMatrix) is diagonal with eigenvalues alpha = (-7 + 24i)/25 at |00>, 1 at |01> and |10>, and beta = (-7 - 24i)/25 at |11>, where alpha, beta and 1 are pairwise distinct. An invariant subspace W therefore contains, together with each of its vectors, its |00> part, its |11> part and its part in the span of |01> and |10>, obtained as explicit combinations of the vector and its images under the first two powers of the diagonal operator. The rotation tensor square sends |00> to (9|00> + 12|01> + 12|10> + 16|11>)/25 and mixes the weight components, so an invariant W that contains |00> or |11> contains every symmetric vector. A case analysis on the weight components of a vector of W outside the line of omega, and then of a vector outside the symmetric tensors, leaves exactly the four subspaces. The dimension three comes from the orthogonal complement of a nonzero vector in the four-dimensional space V.

Neither matrix alone suffices, and the diagonal phases alone do not suffice: every matrix diag(z, 1/z) with z nonzero has a tensor square fixing |01> and |10>, so the line spanned by |01> is invariant under all of them, and the eigenlines of the rotation tensor square are invariant under it. These examples are remarks and are not formalised.

For the group SU(2) this is the classical Clebsch-Gordan decomposition of the tensor square of the two-dimensional representation into the antisymmetric part, spanned by omega, and the irreducible three-dimensional symmetric part; the statement that two explicit elements already force the four subspaces, and the proof in coordinates, are derived here. Combined with the restriction theorem exists_mulEquiv_orthogonal for the line of omega, the isometries of V fixing omega correspond to the isometries of the three-dimensional symmetric part with the same determinant; that combination is not one of the formal statements of this module.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/Unitary/TensorSquareSinglet.phaseMatrix`
- Truth anchor: `D5/S3/Quantum/Algebra/Unitary/TensorSquareSinglet.rotationMatrix`
- Truth anchor: `D5/S3/Quantum/Algebra/Unitary/TensorSquareSinglet.singlet`
- Truth anchor: `D5/S3/Quantum/Algebra/Unitary/TensorSquareSinglet.singlet_invariant_subspaces`
