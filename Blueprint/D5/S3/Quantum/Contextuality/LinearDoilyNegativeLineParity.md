# Odd negative-line parity in linear doilies

## Abstract

Every linear N-qubit doily has an odd number of negative lines.

**Definition 1.1 (Canonical single-qubit labels).**

$$\forall (p: (\operatorname{ZMod}\left(2\right) \times \operatorname{ZMod}\left(2\right))), (\operatorname{canonicalLabel}\left(p\right) = \operatorname{ite}\left((p).1 = (0: \operatorname{ZMod}\left(2\right)), \operatorname{ite}\left((p).2 = (0: \operatorname{ZMod}\left(2\right)), \operatorname{Pauli.I}, \operatorname{Pauli.Z}\right), \operatorname{ite}\left((p).2 = (0: \operatorname{ZMod}\left(2\right)), \operatorname{Pauli.X}, \operatorname{Pauli.Y}\right)\right))$$

*Formalization.* `D5/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity.canonicalLabel` (`✓ std3`).

*Citation.* Axel Muller; Metod Saniga; Alain Giorgetti; Henri de Boutray; Frédéric Holweck (2022). *Multi-qubit doilies: enumeration for all ranks and classification for ranks four and five*. DOI: [10.1016/j.jocs.2022.101853](https://doi.org/10.1016/j.jocs.2022.101853). URL: <https://arxiv.org/abs/2206.03599v2>.

*Commentary.*

The four binary pairs label I, Z, X and Y, with Y = iXZ. The first coordinate is the exponent of X and the second that of Z. These coordinates exchange the two entries of the paper's convention in xiv-MSGDH2.tex, lines 288–295; the observables are the same unsigned Pauli matrices.

**Definition 1.2 (Tensor products of canonical Pauli matrices).**

$$\forall (N: \mathbb{N}), (\forall (v: (\operatorname{Fin}\left(N\right) \to (\operatorname{ZMod}\left(2\right) \times \operatorname{ZMod}\left(2\right)))), (\operatorname{observable}\left(v\right) = \operatorname{wordOp}\left((\lambda (j: \operatorname{Fin}\left(N\right)) \mapsto (\operatorname{canonicalLabel}\left(v\left(j\right)\right)))\right)))$$

*Formalization.* `D5/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity.observable` (`✓ std3`).

*Citation.* Axel Muller; Metod Saniga; Alain Giorgetti; Henri de Boutray; Frédéric Holweck (2022). *Multi-qubit doilies: enumeration for all ranks and classification for ranks four and five*. DOI: [10.1016/j.jocs.2022.101853](https://doi.org/10.1016/j.jocs.2022.101853). URL: <https://arxiv.org/abs/2206.03599v2>.

*Commentary.*

For a binary label v on N qubits, take the tensor product of the matrices specified by canonicalLabel at each coordinate j. The rows and columns are indexed by functions from Fin N to Fin 2. This includes the identity when v is zero. The unsigned tensor products are defined in xiv-MSGDH2.tex, lines 273–283.

**Definition 1.3 (The binary commutation form).**

$$\forall (N: \mathbb{N}), (\forall (v: (\operatorname{Fin}\left(N\right) \to (\operatorname{ZMod}\left(2\right) \times \operatorname{ZMod}\left(2\right)))), (\forall (w: (\operatorname{Fin}\left(N\right) \to (\operatorname{ZMod}\left(2\right) \times \operatorname{ZMod}\left(2\right)))), (\operatorname{B}\left(v, w\right) = \sum_{(j: \operatorname{Fin}\left(N\right))} ((((v\left(j\right)).1) \cdot ((w\left(j\right)).2)) + (((v\left(j\right)).2) \cdot ((w\left(j\right)).1))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity.B` (`✓ std3`).

*Citation.* Axel Muller; Metod Saniga; Alain Giorgetti; Henri de Boutray; Frédéric Holweck (2022). *Multi-qubit doilies: enumeration for all ranks and classification for ranks four and five*. DOI: [10.1016/j.jocs.2022.101853](https://doi.org/10.1016/j.jocs.2022.101853). URL: <https://arxiv.org/abs/2206.03599v2>.

*Commentary.*

The form sums the cross-coordinate products over all qubits in ZMod 2. Two canonical observables commute precisely when this form vanishes. It is the standard symplectic form in xiv-MSGDH2.tex, lines 222–231; in characteristic two subtraction equals addition.

**Definition 1.4 (Nondegenerate four-dimensional binary subspaces).**

$$\forall (N: \mathbb{N}), (\forall (U: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), (\operatorname{Fin}\left(N\right) \to (\operatorname{ZMod}\left(2\right) \times \operatorname{ZMod}\left(2\right)))\right)), (\operatorname{IsLinearDoily}\left(U\right) = ((\operatorname{Module.finrank}\left(\operatorname{ZMod}\left(2\right), \operatorname{CoeSort.coe}\left(U\right)\right) = (4: \mathbb{N})) \land (\forall (u: (\operatorname{Fin}\left(N\right) \to (\operatorname{ZMod}\left(2\right) \times \operatorname{ZMod}\left(2\right)))), ((u \in U) \Rightarrow ((\forall (w: (\operatorname{Fin}\left(N\right) \to (\operatorname{ZMod}\left(2\right) \times \operatorname{ZMod}\left(2\right)))), ((w \in U) \Rightarrow (\operatorname{B}\left(u, w\right) = (0: \operatorname{ZMod}\left(2\right))))) \Rightarrow (u = (0: (\operatorname{Fin}\left(N\right) \to (\operatorname{ZMod}\left(2\right) \times \operatorname{ZMod}\left(2\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity.IsLinearDoily` (`✓ std3`).

*Citation.* Axel Muller; Metod Saniga; Alain Giorgetti; Henri de Boutray; Frédéric Holweck (2022). *Multi-qubit doilies: enumeration for all ranks and classification for ranks four and five*. DOI: [10.1016/j.jocs.2022.101853](https://doi.org/10.1016/j.jocs.2022.101853). URL: <https://arxiv.org/abs/2206.03599v2>.

*Commentary.*

A linear doily is a four-dimensional binary subspace whose restricted symplectic form has zero radical. CoeSort.coe U explicitly denotes the type coercion of U, the underlying type of vectors in U in the dimension formula. The source defines a linear doily as one spanning PG(3,2), in xiv-MSGDH2.tex, lines 1086–1087. Over the binary field its fifteen points exhaust the nonzero vectors of that four-space. A nonzero radical vector would be collinear with all fourteen other points, whereas a point of the doily has six collinear neighbours. Thus the restricted form is nondegenerate. Conversely a nondegenerate binary four-space has the symplectic polar space W(3,2), the doily.

**Definition 1.5 (The nonzero vectors of a subspace).**

$$\forall (N: \mathbb{N}), (\forall (U: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), (\operatorname{Fin}\left(N\right) \to (\operatorname{ZMod}\left(2\right) \times \operatorname{ZMod}\left(2\right)))\right)), (\operatorname{points}\left(U\right) = \operatorname{Finset.filter}\left((\lambda (v: (\operatorname{Fin}\left(N\right) \to (\operatorname{ZMod}\left(2\right) \times \operatorname{ZMod}\left(2\right)))) \mapsto ((v \in U) \land (v \ne (0: (\operatorname{Fin}\left(N\right) \to (\operatorname{ZMod}\left(2\right) \times \operatorname{ZMod}\left(2\right))))))), (\operatorname{Finset.univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(N\right) \to (\operatorname{ZMod}\left(2\right) \times \operatorname{ZMod}\left(2\right)))\right))\right)))$$

*Formalization.* `D5/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity.points` (`✓ std3`).

*Citation.* Axel Muller; Metod Saniga; Alain Giorgetti; Henri de Boutray; Frédéric Holweck (2022). *Multi-qubit doilies: enumeration for all ranks and classification for ranks four and five*. DOI: [10.1016/j.jocs.2022.101853](https://doi.org/10.1016/j.jocs.2022.101853). URL: <https://arxiv.org/abs/2206.03599v2>.

*Commentary.*

The points are exactly the vectors belonging to U other than zero. There is one nonzero vector per projective point over the binary field. This is the projective point description in xiv-MSGDH2.tex, lines 222–225.

**Definition 1.6 (Isotropic triples of points).**

$$\forall (N: \mathbb{N}), (\forall (U: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), (\operatorname{Fin}\left(N\right) \to (\operatorname{ZMod}\left(2\right) \times \operatorname{ZMod}\left(2\right)))\right)), (\operatorname{lines}\left(U\right) = \operatorname{Finset.filter}\left((\lambda (l: \operatorname{Finset}\left((\operatorname{Fin}\left(N\right) \to (\operatorname{ZMod}\left(2\right) \times \operatorname{ZMod}\left(2\right)))\right)) \mapsto ((\operatorname{Finset.card}\left(l\right) = (3: \mathbb{N})) \land (\forall (u: (\operatorname{Fin}\left(N\right) \to (\operatorname{ZMod}\left(2\right) \times \operatorname{ZMod}\left(2\right)))), ((u \in l) \Rightarrow (\forall (v: (\operatorname{Fin}\left(N\right) \to (\operatorname{ZMod}\left(2\right) \times \operatorname{ZMod}\left(2\right)))), ((v \in l) \Rightarrow ((u \ne v) \Rightarrow (((u) + (v) \in l) \land (\operatorname{B}\left(u, v\right) = (0: \operatorname{ZMod}\left(2\right))))))))))), \operatorname{Finset.powerset}\left(\operatorname{points}\left(U\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity.lines` (`✓ std3`).

*Citation.* Axel Muller; Metod Saniga; Alain Giorgetti; Henri de Boutray; Frédéric Holweck (2022). *Multi-qubit doilies: enumeration for all ranks and classification for ranks four and five*. DOI: [10.1016/j.jocs.2022.101853](https://doi.org/10.1016/j.jocs.2022.101853). URL: <https://arxiv.org/abs/2206.03599v2>.

*Commentary.*

Among all subsets of points U, retain the three-element sets such that every pair of distinct vectors has zero symplectic pairing and has its sum in the same set. Each is a triple consisting of u, v and u + v, hence the nonzero vectors of a totally isotropic two-dimensional subspace. The isotropic geometry and its observable interpretation are described in xiv-MSGDH2.tex, lines 225–231 and 306–312.

**Definition 1.7 (The matrix product of a finite set of observables).**

$$\forall (N: \mathbb{N}), (\forall (l: \operatorname{Finset}\left((\operatorname{Fin}\left(N\right) \to (\operatorname{ZMod}\left(2\right) \times \operatorname{ZMod}\left(2\right)))\right)), (\operatorname{lineProduct}\left(l\right) = \operatorname{List.prod}\left(\operatorname{List.map}\left(\operatorname{observable}, \operatorname{Finset.toList}\left(l\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity.lineProduct` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Axel Muller; Metod Saniga; Alain Giorgetti; Henri de Boutray; Frédéric Holweck (2022). *Multi-qubit doilies: enumeration for all ranks and classification for ranks four and five*. DOI: [10.1016/j.jocs.2022.101853](https://doi.org/10.1016/j.jocs.2022.101853). URL: <https://arxiv.org/abs/2206.03599v2>.

*Commentary.*

Convert l to a list, replace each vector by its canonical observable, and multiply the matrices in that order. The definition applies to every finite set l. For an isotropic triple the three matrices commute, so the product is independent of the chosen list order.

**Definition 1.8 (Lines whose matrix product is minus identity).**

$$\forall (N: \mathbb{N}), (\forall (U: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), (\operatorname{Fin}\left(N\right) \to (\operatorname{ZMod}\left(2\right) \times \operatorname{ZMod}\left(2\right)))\right)), (\operatorname{negativeLines}\left(U\right) = \operatorname{Finset.filter}\left((\lambda (l: \operatorname{Finset}\left((\operatorname{Fin}\left(N\right) \to (\operatorname{ZMod}\left(2\right) \times \operatorname{ZMod}\left(2\right)))\right)) \mapsto (\operatorname{lineProduct}\left(l\right) = -((1: \operatorname{Matrix}\left((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)), \mathbb{C}\right))))), \operatorname{lines}\left(U\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity.negativeLines` (`✓ std3`).

*Citation.* Axel Muller; Metod Saniga; Alain Giorgetti; Henri de Boutray; Frédéric Holweck (2022). *Multi-qubit doilies: enumeration for all ranks and classification for ranks four and five*. DOI: [10.1016/j.jocs.2022.101853](https://doi.org/10.1016/j.jocs.2022.101853). URL: <https://arxiv.org/abs/2206.03599v2>.

*Commentary.*

A negative line is a line of U whose product is minus the identity matrix on the N-qubit tensor space. The one in the formula is explicitly a matrix identity, not a complex scalar. This is the sign convention in xiv-MSGDH2.tex, lines 312–314.

**Definition 1.9 (The parity assertion for every number of qubits).**

$$\operatorname{claim} = (\forall (N: \mathbb{N}), (((2: \mathbb{N}) \le N) \Rightarrow (\forall (U: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), (\operatorname{Fin}\left(N\right) \to (\operatorname{ZMod}\left(2\right) \times \operatorname{ZMod}\left(2\right)))\right)), ((\operatorname{IsLinearDoily}\left(U\right)) \Rightarrow (\operatorname{Odd}\left(\operatorname{Finset.card}\left(\operatorname{negativeLines}\left(U\right)\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity.claim` (`✓ std3`).

*Citation.* Axel Muller; Metod Saniga; Alain Giorgetti; Henri de Boutray; Frédéric Holweck (2022). *Multi-qubit doilies: enumeration for all ranks and classification for ranks four and five*. DOI: [10.1016/j.jocs.2022.101853](https://doi.org/10.1016/j.jocs.2022.101853). URL: <https://arxiv.org/abs/2206.03599v2>.

*Commentary.*

For every natural N at least two and every nondegenerate four-dimensional binary subspace U, the natural cardinality of negativeLines U is odd. The source states this conjecture in xiv-MSGDH2.tex, lines 2255–2260. Cardinalities and the dimension in these formulas are natural numbers; neither is cast to an integer or a complex number.

**Theorem 1.10 (Every linear doily has odd negative-line parity).**

$$\forall (N: \mathbb{N}), (((2: \mathbb{N}) \le N) \Rightarrow (\forall (U: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), (\operatorname{Fin}\left(N\right) \to (\operatorname{ZMod}\left(2\right) \times \operatorname{ZMod}\left(2\right)))\right)), ((\operatorname{IsLinearDoily}\left(U\right)) \Rightarrow (\operatorname{Odd}\left(\operatorname{Finset.card}\left(\operatorname{negativeLines}\left(U\right)\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity.result` (`✓ std3`). ∎

*Resolves.* `Problems/muller-saniga-giorgetti-de-boutray-holweck-2022-linear-doily-odd-negative-lines` (proved) by `D5/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"muller-saniga-giorgetti-de-boutray-holweck-2022-linear-doily-odd-negative-lines","declaration_gid":"D5/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Axel Muller; Metod Saniga; Alain Giorgetti; Henri de Boutray; Frédéric Holweck (2022). *Multi-qubit doilies: enumeration for all ranks and classification for ranks four and five*. DOI: [10.1016/j.jocs.2022.101853](https://doi.org/10.1016/j.jocs.2022.101853). URL: <https://arxiv.org/abs/2206.03599v2>.

*Commentary.*

For two single-qubit labels, lift each binary coordinate to its natural representative zero or one. Form a residue modulo four by adding the coordinate products of the two labels, subtracting the coordinate product of their binary sum, and adding twice the second coordinate of the first label times the first coordinate of the second. The natural coordinate products are cast into ZMod 4 before adding or subtracting them, and the last product is multiplied there by two. The frozen Pauli letter multiplication and commutation identities, with binary labels and scalars normalized over the sixteen ordered label pairs, give the product as i to this exponent times the matrix of the sum. The commutation sign is plus one for zero binary symplectic pairing and minus one otherwise. Tensoring these identities gives the multiplication scalar and commutation sign for N qubits. The canonical Pauli word unit is its own inverse, so each observable squares to the identity. The square of the multiplication scalar is the sign of the symplectic pairing. For an isotropic pair this scalar is therefore plus or minus one. Every line is a triple of distinct nonzero vectors u, v and u + v, so its matrix product is plus or minus the identity.

The binary form is bilinear, symmetric and alternating. Its restriction to U is nondegenerate by the defining radical condition. A symplectic basis therefore exists; dimension four forces exactly two symplectic pairs. Reorder that basis to obtain a linear equivalence e from Fin 4 → ZMod 2 to U, with coordinate pairings between positions zero and one and between positions two and three equal to one, and all other basis pairings zero. Thus the transported form on coordinates a and b is a 0 times b 1 plus a 1 times b 0 plus a 2 times b 3 plus a 3 times b 2.

In this binary coordinate four-space, enumerate the fifteen distinct isotropic triples using the following ordered pairs, with each bit string giving coordinates zero through three: (0001,0100), (0001,1000), (0001,1100), (0010,0100), (0010,1000), (0010,1100), (0011,0100), (0011,1000), (0011,1100), (0101,1010), (0101,1011), (0110,1001), (0110,1011), (0111,1001), (0111,1010). Each representative is nonzero, the pair is distinct and orthogonal, and its sum is the third point. The fifteen triples are distinct and contain every triple generated by distinct nonzero orthogonal vectors. For any four single-qubit labels, evaluate these fifteen representative pairs by taking their binary linear combinations. The sum of their multiplication exponents in ZMod 4 equals twice the natural representative of the local symplectic pairing of the first two labels, cast into ZMod 4. This identity follows by checking all 256 assignments of the four labels.

The additive character on ZMod 4 sending k to i raised to its natural representative converts addition into multiplication of fourth roots of unity. Its finite-product law and the local exponent identity make the product of the fifteen local scalars equal to the sign of the first local basis pairing. Linearity of e expresses each embedded vector at a qubit as the corresponding linear combination of the four basis labels at that qubit. Exchange the finite products over the fifteen pairs and over the N qubits. Multiplying the local signs adds their binary pairings, giving the sign of the global pairing of the first symplectic basis pair. That pairing is one, so the product of all fifteen multiplication scalars is minus one.

Orthogonal vectors have commuting observables. Permuting the list of an isotropic triple therefore preserves its matrix product; multiplication of the first two observables followed by the square identity for their sum shows that this product is its multiplication scalar times the identity. Transport the fifteen coordinate triples through e. Every resulting triple is a line of U, every line of U arises in this way, and injectivity of e keeps distinct triples distinct. Thus this transport is a bijection onto lines U.

For a finite family of complex signs, its product is minus one exactly when the number of entries equal to minus one is odd: the product is minus one raised to that natural cardinality. Multiplication of the identity matrix by a complex scalar is injective, since the identity matrix is nonzero. Apply this to the fifteen scalars. The matrix sign of each transported line shows that its scalar is plus or minus one, and the line is negative exactly when its scalar is minus one. Their total product is minus one, so an odd number of the scalars are negative. The line bijection identifies this count with the cardinality of negativeLines U. Choosing the symplectic equivalence for each U proves the assertion for every N at least two.

## References

- Truth anchor: `D5/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity.B`
- Truth anchor: `D5/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity.IsLinearDoily`
- Truth anchor: `D5/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity.canonicalLabel`
- Truth anchor: `D5/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity.claim`
- Truth anchor: `D5/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity.lineProduct`
- Truth anchor: `D5/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity.lines`
- Truth anchor: `D5/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity.negativeLines`
- Truth anchor: `D5/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity.observable`
- Truth anchor: `D5/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity.points`
- Truth anchor: `D5/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity.result`
- Dependency: [D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm](../Information/BinaryStabilizerGraphNormalForm.md)
- Dependency: [D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation](../Measurement/StabilizerPovmMaximalEntanglementRefutation.md)
