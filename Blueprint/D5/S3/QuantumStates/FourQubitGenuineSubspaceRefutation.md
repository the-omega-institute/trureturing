# Antipin's four-qubit subspace need not be genuinely entangled

## Abstract

The four-qubit subspace obtained from Antipin's vectors (35) and substitutions (39)–(40) contains a nonzero product vector at a parameter tuple in (0,1)⁷.

The four parties, in order, are A₁, A₂, B₁ and B₂. Indices in Fin n start at zero; the seven entries of the real parameter function correspond to λ₁ through λ₇ in the source. A centered dot denotes complex scalar multiplication of a vector. The notation ![a₀, …, aₙ₋₁] denotes the function on Fin n with those entries. All coefficient functions and tensor products are over ℂ.

**Definition 1.1 (The two qubit labels).**

$$\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit} = \operatorname{Fin}\left(2\right)$$

*Formalization.* `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.Bit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin 2 consists of the labels zero and one.

**Definition 1.2 (The four party labels).**

$$\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Party} = \operatorname{Fin}\left(4\right)$$

*Formalization.* `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.Party` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Labels zero through three denote A₁, A₂, B₁ and B₂, respectively.

**Definition 1.3 (A qubit coefficient space).**

$$\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Qubit} = (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit} \to \mathbb{C})$$

*Formalization.* `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.Qubit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A qubit is a complex-valued function on its two basis labels.

**Definition 1.4 (A ququart coefficient space).**

$$\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Ququart} = (\operatorname{Fin}\left(4\right) \to \mathbb{C})$$

*Formalization.* `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.Ququart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A ququart is a complex-valued function on four basis labels.

**Definition 1.5 (The tensor product of two qubits).**

$$\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.TwoQubit} = \operatorname{TensorProduct}\left(\mathbb{C}, \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Qubit}, \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Qubit}\right)$$

*Formalization.* `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.TwoQubit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two-qubit space is TensorProduct ℂ Qubit Qubit.

**Definition 1.6 (Four-qubit configurations).**

$$\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Config} = (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit} \times (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit} \times (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit} \times \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit})))$$

*Formalization.* `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.Config` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A configuration is the nested tuple (a,(b,(c,d))) in party order A₁,A₂,B₁,B₂.

**Definition 1.7 (Four-qubit coefficient functions).**

$$\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.State} = (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Config} \to \mathbb{C})$$

*Formalization.* `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.State` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A state vector assigns a complex amplitude to each four-qubit configuration; no normalization is imposed.

**Definition 1.8 (Two-ququart coefficient functions).**

$$\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Original} = ((\operatorname{Fin}\left(4\right) \times \operatorname{Fin}\left(4\right)) \to \mathbb{C})$$

*Formalization.* `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.Original` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original vectors are coefficient functions on pairs of ququart labels.

**Definition 1.9 (Reading the qubit of each party).**

$$\forall (q: \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Config}), (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.coordinate}\left(q\right) = ![q.1, q.2.1, q.2.2.1, q.2.2.2])$$

*Formalization.* `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.coordinate` (`✓ std3`).

*Citation.* K. V. Antipin (2021). *Construction of genuinely multipartite entangled subspaces and the associated bounds on entanglement measures for mixed states*. DOI: [10.1088/1751-8121/ac37e5](https://doi.org/10.1088/1751-8121/ac37e5). URL: <https://arxiv.org/abs/2104.09664v1>.

*Commentary.*

The four entries of a configuration give the coordinates at A₁,A₂,B₁ and B₂, in that order.

**Definition 1.10 (Product vectors across a chosen cut).**

$$\forall (s: \operatorname{Finset}\left(\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Party}\right)), (\forall (z: \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.State}), ((\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.IsProductAcross}\left(s, z\right)) \Leftrightarrow (\exists (f: ((\{p: \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Party} // p \in s\} \to \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit}) \to \mathbb{C})), (\exists (g: ((\{p: \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Party} // \neg (p \in s)\} \to \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit}) \to \mathbb{C})), (\forall (q: \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Config}), (z\left(q\right) = (f\left(\lambda (p: \{p: \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Party} // p \in s\}) \mapsto (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.coordinate}\left(q, \operatorname{Subtype.val}\left(p\right)\right))\right)) \cdot (g\left(\lambda (p: \{p: \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Party} // \neg (p \in s)\}) \mapsto (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.coordinate}\left(q, \operatorname{Subtype.val}\left(p\right)\right))\right))))))))$$

*Formalization.* `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.IsProductAcross` (`✓ std3`).

*Citation.* K. V. Antipin (2021). *Construction of genuinely multipartite entangled subspaces and the associated bounds on entanglement measures for mixed states*. DOI: [10.1088/1751-8121/ac37e5](https://doi.org/10.1088/1751-8121/ac37e5). URL: <https://arxiv.org/abs/2104.09664v1>.

*Commentary.*

Section II.A, equation (2), defines a product across a bipartition. Here the two factors are arbitrary complex coefficient functions on assignments to the parties in s and outside s. Subtype.val forgets the membership proof. This predicate alone permits empty parts and the zero vector; the GES condition restricts the cut and excludes zero.

**Definition 1.11 (Genuinely entangled subspaces).**

$$\forall (W: \operatorname{Submodule}\left(\mathbb{C}, \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.State}\right)), ((\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.IsGES}\left(W\right)) \Leftrightarrow (\forall (z: \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.State}), ((z \in W) \Rightarrow ((z \ne 0) \Rightarrow (\forall (s: \operatorname{Finset}\left(\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Party}\right)), ((\operatorname{Finset.Nonempty}\left(s\right)) \Rightarrow ((s \ne (\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Party}\right))) \Rightarrow (\neg (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.IsProductAcross}\left(s, z\right))))))))))$$

*Formalization.* `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.IsGES` (`✓ std3`).

*Citation.* K. V. Antipin (2021). *Construction of genuinely multipartite entangled subspaces and the associated bounds on entanglement measures for mixed states*. DOI: [10.1088/1751-8121/ac37e5](https://doi.org/10.1088/1751-8121/ac37e5). URL: <https://arxiv.org/abs/2104.09664v1>.

*Commentary.*

Section II.A calls a subspace genuinely entangled when every nonzero vector is genuinely multipartite entangled. Every nonempty proper finite set of parties determines a bipartition, and no such cut may admit a product factorization. The seven bipartitions occur twice, once for each choice of side.

**Definition 1.12 (The two-ququart basis vectors).**

$$\forall (a: \operatorname{Fin}\left(4\right)), (\forall (b: \operatorname{Fin}\left(4\right)), ((\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket44}\left(a, b\right): \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Original}) = \operatorname{Pi.single}\left((a, b), (1: \mathbb{C})\right)))$$

*Formalization.* `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.ket44` (`✓ std3`).

*Citation.* K. V. Antipin (2021). *Construction of genuinely multipartite entangled subspaces and the associated bounds on entanglement measures for mixed states*. DOI: [10.1088/1751-8121/ac37e5](https://doi.org/10.1088/1751-8121/ac37e5). URL: <https://arxiv.org/abs/2104.09664v1>.

*Commentary.*

Pi.single (a,b) 1 is the coefficient function equal to one at (a,b) and zero at every other pair. It represents |a⟩ ⊗ |b⟩ in equations (35a)–(35g).

**Definition 1.13 (The two-qubit basis tensors).**

$$\forall (a: \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit}), (\forall (b: \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit}), (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket22}\left(a, b\right) = \operatorname{TensorProduct.tmul}\left(\mathbb{C}, (\operatorname{Pi.single}\left(a, (1: \mathbb{C})\right): \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Qubit}), (\operatorname{Pi.single}\left(b, (1: \mathbb{C})\right): \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Qubit})\right)))$$

*Formalization.* `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.ket22` (`✓ std3`).

*Citation.* K. V. Antipin (2021). *Construction of genuinely multipartite entangled subspaces and the associated bounds on entanglement measures for mixed states*. DOI: [10.1088/1751-8121/ac37e5](https://doi.org/10.1088/1751-8121/ac37e5). URL: <https://arxiv.org/abs/2104.09664v1>.

*Commentary.*

TensorProduct.tmul forms the pure tensor of the two single-qubit basis vectors. These are the |ab⟩ vectors in substitutions (39) and (40).

**Definition 1.14 (The seven vectors in equation (35)).**

$$\forall (\lambda: (\operatorname{Fin}\left(7\right) \to \mathbb{R})), (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.v35}\left(\lambda\right) = ![(((\operatorname{Real.sqrt}\left(\lambda\left(0\right)\right): \mathbb{C})) \cdot (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket44}\left(0, 0\right))) + (((\operatorname{Real.sqrt}\left((1) - (\lambda\left(0\right))\right): \mathbb{C})) \cdot (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket44}\left(2, 1\right))), (((\operatorname{Real.sqrt}\left(\lambda\left(1\right)\right): \mathbb{C})) \cdot (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket44}\left(1, 2\right))) + (((\operatorname{Real.sqrt}\left((1) - (\lambda\left(1\right))\right): \mathbb{C})) \cdot (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket44}\left(3, 3\right))), (((\operatorname{Real.sqrt}\left(\lambda\left(2\right)\right): \mathbb{C})) \cdot (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket44}\left(0, 1\right))) + (((\operatorname{Real.sqrt}\left((1) - (\lambda\left(2\right))\right): \mathbb{C})) \cdot (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket44}\left(3, 2\right))), (((\operatorname{Real.sqrt}\left(\lambda\left(3\right)\right): \mathbb{C})) \cdot (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket44}\left(3, 0\right))) + (((\operatorname{Real.sqrt}\left((1) - (\lambda\left(3\right))\right): \mathbb{C})) \cdot (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket44}\left(2, 2\right))), (((\operatorname{Real.sqrt}\left(\lambda\left(4\right)\right): \mathbb{C})) \cdot (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket44}\left(1, 1\right))) + (((\operatorname{Real.sqrt}\left((1) - (\lambda\left(4\right))\right): \mathbb{C})) \cdot (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket44}\left(0, 3\right))), (((\operatorname{Real.sqrt}\left(\lambda\left(5\right)\right): \mathbb{C})) \cdot (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket44}\left(1, 0\right))) + (((\operatorname{Real.sqrt}\left((1) - (\lambda\left(5\right))\right): \mathbb{C})) \cdot (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket44}\left(2, 3\right))), (((\operatorname{Real.sqrt}\left(\lambda\left(6\right)\right): \mathbb{C})) \cdot (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket44}\left(2, 0\right))) + (((\operatorname{Real.sqrt}\left((1) - (\lambda\left(6\right))\right): \mathbb{C})) \cdot (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket44}\left(3, 1\right)))])$$

*Formalization.* `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.v35` (`✓ std3`).

*Citation.* K. V. Antipin (2021). *Construction of genuinely multipartite entangled subspaces and the associated bounds on entanglement measures for mixed states*. DOI: [10.1088/1751-8121/ac37e5](https://doi.org/10.1088/1751-8121/ac37e5). URL: <https://arxiv.org/abs/2104.09664v1>.

*Commentary.*

These are equations (35a)–(35g), in their printed order. Real.sqrt is the real square root, and each real amplitude is cast to ℂ before acting on a vector. The definition accepts every real parameter function; the conjecture below requires every parameter to lie strictly between zero and one.

**Definition 1.15 (The four images in substitution (39)).**

$$\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.columns39} = ![((\frac{1}{6}: \mathbb{C})) \cdot ((((((5: \mathbb{C})) \cdot (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket22}\left(0, 0\right))) - (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket22}\left(0, 1\right))) + (((3: \mathbb{C})) \cdot (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket22}\left(1, 0\right)))) - (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket22}\left(1, 1\right))), ((\frac{1}{6}: \mathbb{C})) \cdot ((((-(\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket22}\left(0, 0\right))) + (((5: \mathbb{C})) \cdot (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket22}\left(0, 1\right)))) + (((3: \mathbb{C})) \cdot (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket22}\left(1, 0\right)))) - (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket22}\left(1, 1\right))), ((\frac{1}{2}: \mathbb{C})) \cdot ((((\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket22}\left(0, 0\right)) + (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket22}\left(0, 1\right))) - (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket22}\left(1, 0\right))) + (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket22}\left(1, 1\right))), ((\frac{1}{6}: \mathbb{C})) \cdot ((((-(\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket22}\left(0, 0\right))) - (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket22}\left(0, 1\right))) + (((3: \mathbb{C})) \cdot (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket22}\left(1, 0\right)))) + (((5: \mathbb{C})) \cdot (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket22}\left(1, 1\right))))]$$

*Formalization.* `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.columns39` (`✓ std3`).

*Citation.* K. V. Antipin (2021). *Construction of genuinely multipartite entangled subspaces and the associated bounds on entanglement measures for mixed states*. DOI: [10.1088/1751-8121/ac37e5](https://doi.org/10.1088/1751-8121/ac37e5). URL: <https://arxiv.org/abs/2104.09664v1>.

*Commentary.*

These four two-qubit tensors are the images of |0⟩, |1⟩, |2⟩ and |3⟩ of the first ququart, exactly as in equation (39).

**Definition 1.16 (The four images in substitution (40)).**

$$\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.columns40} = ![((\frac{1}{3}: \mathbb{C})) \cdot (((-(\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket22}\left(0, 0\right))) + (((2: \mathbb{C})) \cdot (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket22}\left(0, 1\right)))) + (((2: \mathbb{C})) \cdot (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket22}\left(1, 1\right)))), ((\frac{1}{3}: \mathbb{C})) \cdot (((((2: \mathbb{C})) \cdot (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket22}\left(0, 0\right))) - (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket22}\left(0, 1\right))) + (((2: \mathbb{C})) \cdot (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket22}\left(1, 1\right)))), \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket22}\left(1, 0\right), ((\frac{1}{3}: \mathbb{C})) \cdot (((((2: \mathbb{C})) \cdot (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket22}\left(0, 0\right))) + (((2: \mathbb{C})) \cdot (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket22}\left(0, 1\right)))) - (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.ket22}\left(1, 1\right)))]$$

*Formalization.* `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.columns40` (`✓ std3`).

*Citation.* K. V. Antipin (2021). *Construction of genuinely multipartite entangled subspaces and the associated bounds on entanglement measures for mixed states*. DOI: [10.1088/1751-8121/ac37e5](https://doi.org/10.1088/1751-8121/ac37e5). URL: <https://arxiv.org/abs/2104.09664v1>.

*Commentary.*

These are the four images of the second ququart's basis vectors, in equation (40).

**Definition 1.17 (The linear extension of substitution (39)).**

$$\begin{aligned}\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.substitution39} = \operatorname{Module.Basis.constr}\left(\operatorname{Pi.basisFun}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right), \mathbb{C}, \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.columns39}\right)\\\forall (a: \operatorname{Fin}\left(4\right)), (\operatorname{Pi.basisFun}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right)\left(a\right) = (\operatorname{Pi.single}\left(a, (1: \mathbb{C})\right): \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Ququart}))\\\forall (z: \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Ququart}), (\operatorname{Module.Basis.constr}\left(\operatorname{Pi.basisFun}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right), \mathbb{C}, \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.columns39}\right)\left(z\right) = \sum_{(a: \operatorname{Fin}\left(4\right))} ((z\left(a\right)) \cdot (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.columns39}\left(a\right))))\end{aligned}$$

*Formalization.* `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.substitution39` (`✓ std3`).

*Citation.* K. V. Antipin (2021). *Construction of genuinely multipartite entangled subspaces and the associated bounds on entanglement measures for mixed states*. DOI: [10.1088/1751-8121/ac37e5](https://doi.org/10.1088/1751-8121/ac37e5). URL: <https://arxiv.org/abs/2104.09664v1>.

*Commentary.*

Module.Basis.constr extends the prescribed columns linearly from Pi.basisFun, the standard basis of complex functions on Fin 4. Its action is the sum of each input coefficient times its column.

**Definition 1.18 (The linear extension of substitution (40)).**

$$\begin{aligned}\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.substitution40} = \operatorname{Module.Basis.constr}\left(\operatorname{Pi.basisFun}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right), \mathbb{C}, \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.columns40}\right)\\\forall (a: \operatorname{Fin}\left(4\right)), (\operatorname{Pi.basisFun}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right)\left(a\right) = (\operatorname{Pi.single}\left(a, (1: \mathbb{C})\right): \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Ququart}))\\\forall (z: \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Ququart}), (\operatorname{Module.Basis.constr}\left(\operatorname{Pi.basisFun}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right), \mathbb{C}, \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.columns40}\right)\left(z\right) = \sum_{(a: \operatorname{Fin}\left(4\right))} ((z\left(a\right)) \cdot (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.columns40}\left(a\right))))\end{aligned}$$

*Formalization.* `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.substitution40` (`✓ std3`).

*Citation.* K. V. Antipin (2021). *Construction of genuinely multipartite entangled subspaces and the associated bounds on entanglement measures for mixed states*. DOI: [10.1088/1751-8121/ac37e5](https://doi.org/10.1088/1751-8121/ac37e5). URL: <https://arxiv.org/abs/2104.09664v1>.

*Commentary.*

The second substitution is the linear extension of the four columns in equation (40), using the same standard ququart basis.

**Definition 1.19 (The tensor basis of two qubits).**

$$\begin{aligned}\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.twoBasis} = \operatorname{Module.Basis.tensorProduct}\left(\operatorname{Pi.basisFun}\left(\mathbb{C}, \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit}\right), \operatorname{Pi.basisFun}\left(\mathbb{C}, \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit}\right)\right)\\\forall (a: \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit}), (\operatorname{Pi.basisFun}\left(\mathbb{C}, \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit}\right)\left(a\right) = (\operatorname{Pi.single}\left(a, (1: \mathbb{C})\right): \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Qubit}))\\\forall (a: \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit}), (\forall (b: \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit}), (\operatorname{Module.Basis.tensorProduct}\left(\operatorname{Pi.basisFun}\left(\mathbb{C}, \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit}\right), \operatorname{Pi.basisFun}\left(\mathbb{C}, \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit}\right)\right)\left((a, b)\right) = \operatorname{TensorProduct.tmul}\left(\mathbb{C}, \operatorname{Pi.basisFun}\left(\mathbb{C}, \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit}\right)\left(a\right), \operatorname{Pi.basisFun}\left(\mathbb{C}, \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit}\right)\left(b\right)\right)))\end{aligned}$$

*Formalization.* `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.twoBasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Module.Basis.tensorProduct assigns the tensor of the two basis vectors to a pair of labels. Pi.basisFun assigns Pi.single a 1 to label a. Thus the tensor basis has the same order as |00⟩, |01⟩, |10⟩, |11⟩.

**Definition 1.20 (Coordinates of the two-ququart tensor product).**

$$\begin{aligned}\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.inputCoordinates} = \operatorname{Module.Basis.equivFun}\left(\operatorname{Module.Basis.tensorProduct}\left(\operatorname{Pi.basisFun}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right), \operatorname{Pi.basisFun}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right)\right)\right)\\\forall (t: \operatorname{TensorProduct}\left(\mathbb{C}, \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Ququart}, \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Ququart}\right)), (\forall (p: (\operatorname{Fin}\left(4\right) \times \operatorname{Fin}\left(4\right))), (\operatorname{Module.Basis.equivFun}\left(\operatorname{Module.Basis.tensorProduct}\left(\operatorname{Pi.basisFun}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right), \operatorname{Pi.basisFun}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right)\right)\right)\left(t, p\right) = \operatorname{Module.Basis.repr}\left(\operatorname{Module.Basis.tensorProduct}\left(\operatorname{Pi.basisFun}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right), \operatorname{Pi.basisFun}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right)\right)\right)\left(t, p\right)))\\\forall (a: \operatorname{Fin}\left(4\right)), (\forall (b: \operatorname{Fin}\left(4\right)), (\operatorname{Module.Basis.tensorProduct}\left(\operatorname{Pi.basisFun}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right), \operatorname{Pi.basisFun}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right)\right)\left((a, b)\right) = \operatorname{TensorProduct.tmul}\left(\mathbb{C}, (\operatorname{Pi.single}\left(a, (1: \mathbb{C})\right): \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Ququart}), (\operatorname{Pi.single}\left(b, (1: \mathbb{C})\right): \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Ququart})\right)))\\\forall (u: \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Ququart}), (\forall (v: \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Ququart}), (\forall (a: \operatorname{Fin}\left(4\right)), (\forall (b: \operatorname{Fin}\left(4\right)), (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.inputCoordinates}\left(\operatorname{TensorProduct.tmul}\left(\mathbb{C}, u, v\right), (a, b)\right) = (u\left(a\right)) \cdot (v\left(b\right))))))\end{aligned}$$

*Formalization.* `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.inputCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Module.Basis.equivFun gives the coefficients in the tensor product of the standard ququart bases. Its value at a label is Module.Basis.repr at that label. In particular, a pure tensor has coefficient u(a)v(b) at (a,b).

**Definition 1.21 (Coordinates in four-qubit party order).**

$$\begin{aligned}\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.outputCoordinates} = \operatorname{Module.Basis.equivFun}\left(\operatorname{Module.Basis.reindex}\left(\operatorname{Module.Basis.tensorProduct}\left(\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.twoBasis}, \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.twoBasis}\right), \operatorname{Equiv.prodAssoc}\left(\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit}, \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit}, (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit} \times \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit})\right)\right)\right)\\\forall (q: \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Config}), (\operatorname{Module.Basis.reindex}\left(\operatorname{Module.Basis.tensorProduct}\left(\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.twoBasis}, \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.twoBasis}\right), \operatorname{Equiv.prodAssoc}\left(\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit}, \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit}, (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit} \times \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit})\right)\right)\left(q\right) = \operatorname{Module.Basis.tensorProduct}\left(\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.twoBasis}, \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.twoBasis}\right)\left(\operatorname{Equiv.symm}\left(\operatorname{Equiv.prodAssoc}\left(\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit}, \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit}, (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit} \times \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit})\right)\right)\left(q\right)\right))\\\forall (a: \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit}), (\forall (b: \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit}), (\forall (c: \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit}), (\forall (d: \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit}), (\operatorname{Equiv.prodAssoc}\left(\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit}, \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit}, (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit} \times \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit})\right)\left(((a, b), (c, d))\right) = (a, (b, (c, d)))))))\\\forall (u: \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.TwoQubit}), (\forall (v: \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.TwoQubit}), (\forall (a: \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit}), (\forall (b: \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit}), (\forall (c: \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit}), (\forall (d: \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Bit}), (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.outputCoordinates}\left(\operatorname{TensorProduct.tmul}\left(\mathbb{C}, u, v\right), (a, (b, (c, d)))\right) = (\operatorname{Module.Basis.equivFun}\left(\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.twoBasis}\right)\left(u, (a, b)\right)) \cdot (\operatorname{Module.Basis.equivFun}\left(\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.twoBasis}\right)\left(v, (c, d)\right))))))))\end{aligned}$$

*Formalization.* `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.outputCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The tensor product of two two-qubit bases first has labels ((a,b),(c,d)). Equiv.prodAssoc changes these to (a,(b,(c,d))). Module.Basis.reindex uses the inverse change on a new label, and Module.Basis.equivFun takes the coefficients in that basis. This gives exactly the configuration order A₁,A₂,B₁,B₂.

**Definition 1.22 (Applying the two substitutions to their factors).**

$$\begin{aligned}\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.factorwise} = \operatorname{LinearMap.comp}\left(\operatorname{LinearEquiv.toLinearMap}\left(\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.outputCoordinates}\right), \operatorname{LinearMap.comp}\left(\operatorname{TensorProduct.map}\left(\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.substitution39}, \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.substitution40}\right), \operatorname{LinearEquiv.toLinearMap}\left(\operatorname{LinearEquiv.symm}\left(\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.inputCoordinates}\right)\right)\right)\right)\\\forall (u: \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Ququart}), (\forall (v: \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.Ququart}), (\operatorname{TensorProduct.map}\left(\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.substitution39}, \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.substitution40}\right)\left(\operatorname{TensorProduct.tmul}\left(\mathbb{C}, u, v\right)\right) = \operatorname{TensorProduct.tmul}\left(\mathbb{C}, \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.substitution39}\left(u\right), \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.substitution40}\left(v\right)\right)))\end{aligned}$$

*Formalization.* `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.factorwise` (`✓ std3`).

*Citation.* K. V. Antipin (2021). *Construction of genuinely multipartite entangled subspaces and the associated bounds on entanglement measures for mixed states*. DOI: [10.1088/1751-8121/ac37e5](https://doi.org/10.1088/1751-8121/ac37e5). URL: <https://arxiv.org/abs/2104.09664v1>.

*Commentary.*

Convert the input coefficient function into a two-ququart tensor, apply substitution (39) to its first factor and substitution (40) to its second, then take four-qubit coordinates. TensorProduct.map is the linear map whose value on each pure tensor is the tensor of the two images.

**Definition 1.23 (The seven transformed four-qubit vectors).**

$$\forall (\lambda: (\operatorname{Fin}\left(7\right) \to \mathbb{R})), (\forall (i: \operatorname{Fin}\left(7\right)), (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.transformed}\left(\lambda, i\right) = \operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.factorwise}\left(\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.v35}\left(\lambda, i\right)\right)))$$

*Formalization.* `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.transformed` (`✓ std3`).

*Citation.* K. V. Antipin (2021). *Construction of genuinely multipartite entangled subspaces and the associated bounds on entanglement measures for mixed states*. DOI: [10.1088/1751-8121/ac37e5](https://doi.org/10.1088/1751-8121/ac37e5). URL: <https://arxiv.org/abs/2104.09664v1>.

*Commentary.*

Each vector in (35) is transformed by the same pair of substitutions (39)–(40).

**Definition 1.24 (The parameter-dependent subspace).**

$$\forall (\lambda: (\operatorname{Fin}\left(7\right) \to \mathbb{R})), (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.S}\left(\lambda\right) = \operatorname{Submodule.span}\left(\mathbb{C}, \operatorname{Set.range}\left(\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.transformed}\left(\lambda\right)\right)\right))$$

*Formalization.* `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.S` (`✓ std3`).

*Citation.* K. V. Antipin (2021). *Construction of genuinely multipartite entangled subspaces and the associated bounds on entanglement measures for mixed states*. DOI: [10.1088/1751-8121/ac37e5](https://doi.org/10.1088/1751-8121/ac37e5). URL: <https://arxiv.org/abs/2104.09664v1>.

*Commentary.*

Set.range collects the seven transformed vectors, and Submodule.span takes their complex linear span. The subspace is defined for every real parameter tuple.

**Definition 1.25 (The universal four-qubit GES conjecture).**

$$(\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.claim}) \Leftrightarrow (\forall (\lambda: (\operatorname{Fin}\left(7\right) \to \mathbb{R})), ((\forall (i: \operatorname{Fin}\left(7\right)), ((0 < \lambda\left(i\right)) \land (\lambda\left(i\right) < 1))) \Rightarrow (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.IsGES}\left(\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.S}\left(\lambda\right)\right))))$$

*Formalization.* `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.claim` (`✓ std3`).

*Citation.* K. V. Antipin (2021). *Construction of genuinely multipartite entangled subspaces and the associated bounds on entanglement measures for mixed states*. DOI: [10.1088/1751-8121/ac37e5](https://doi.org/10.1088/1751-8121/ac37e5). URL: <https://arxiv.org/abs/2104.09664v1>.

*Commentary.*

At the end of §III.B.2, page 8, the source conjectures that equations (35), (39) and (40) determine a GES for any set of parameter values. The parameters are restricted by 0 < λᵢ < 1, as stated beside (35). This is the assertion for every such tuple, beyond the separately discussed tuple with all entries one half.

**Theorem 1.26 (A nonzero product vector in the transformed span).**

$$\neg (\operatorname{D5.S3.QuantumStates.FourQubitGenuineSubspaceRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/antipin-2021-four-qubit-genuinely-entangled-subspace-refutation` (refuted) by `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"antipin-2021-four-qubit-genuinely-entangled-subspace-refutation","declaration_gid":"D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* K. V. Antipin (2021). *Construction of genuinely multipartite entangled subspaces and the associated bounds on entanglement measures for mixed states*. DOI: [10.1088/1751-8121/ac37e5](https://doi.org/10.1088/1751-8121/ac37e5). URL: <https://arxiv.org/abs/2104.09664v1>.

*Commentary.*

Take λ = (1/2,16/25,1/2,1/2,1/17,1/2,1/2). Every entry is strictly between zero and one. In the source's numbering, form the linear combination 3√2(v₁ + v₃ + v₄ + v₆ + v₇) + 5v₂ + 3√17 v₅ of the vectors (35). After substitutions (39)–(40), it is y = (1/3)(25|000⟩ + |001⟩ + |010⟩ + 13|011⟩ + 15|100⟩ + 6|101⟩ + 7|110⟩ + 10|111⟩) ⊗ (|0⟩ + |1⟩).

Thus y belongs to S at this parameter tuple. Its coefficient at |0000⟩ is 25/3, so it is nonzero. Its first factor is on A₁,A₂,B₁ and its second factor is on B₂, giving a product across {A₁,A₂,B₁} | {B₂}. This nonzero product vector contradicts the GES condition and refutes the universal conjecture.

## References

- Truth anchor: `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.Bit`
- Truth anchor: `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.Config`
- Truth anchor: `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.IsGES`
- Truth anchor: `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.IsProductAcross`
- Truth anchor: `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.Original`
- Truth anchor: `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.Party`
- Truth anchor: `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.Qubit`
- Truth anchor: `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.Ququart`
- Truth anchor: `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.S`
- Truth anchor: `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.State`
- Truth anchor: `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.TwoQubit`
- Truth anchor: `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.claim`
- Truth anchor: `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.columns39`
- Truth anchor: `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.columns40`
- Truth anchor: `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.coordinate`
- Truth anchor: `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.factorwise`
- Truth anchor: `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.inputCoordinates`
- Truth anchor: `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.ket22`
- Truth anchor: `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.ket44`
- Truth anchor: `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.outputCoordinates`
- Truth anchor: `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.result`
- Truth anchor: `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.substitution39`
- Truth anchor: `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.substitution40`
- Truth anchor: `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.transformed`
- Truth anchor: `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.twoBasis`
- Truth anchor: `D5/S3/QuantumStates/FourQubitGenuineSubspaceRefutation.v35`
