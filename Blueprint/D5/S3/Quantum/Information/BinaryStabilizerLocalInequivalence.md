# A state stabilized by binary operators that is not locally a stabilizer state

## Abstract

The six-qubit state v = sum over j of (|e_j> - |complement of e_j>) is, up to a factor, the only common +1 eigenvector of four tensor products of binary operators, yet no Pauli stabilizer state is locally equivalent to it. This refutes the conjecture of E. Descamps and B. Dakic (arXiv:2309.09815) that every state stabilized by binary operators and the identity is locally equivalent to a standard stabilizer state.

**Definition 1.1 (Binary operators).**

$$\operatorname{binaryOp}\left(\theta, \varphi\right) = \operatorname{cos}\left(\theta\right) \cdot \mathrm{Z} + \operatorname{sin}\left(\theta\right) \cdot (\operatorname{cos}\left(\varphi\right) \cdot \mathrm{X} + \operatorname{sin}\left(\varphi\right) \cdot \mathrm{Y})$$

*Formalization.* `D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.binaryOp` (`✓ std3`).

*Citation.* Éloi Descamps, Borivoje Dakić (2024). *On the stabilizer formalism and its generalization*. DOI: [10.1088/1751-8121/ad8607](https://doi.org/10.1088/1751-8121/ad8607). URL: <https://arxiv.org/abs/2309.09815v1>.

*Commentary.*

The binary operator A(theta, phi) = cos(theta) Z + sin(theta) (cos(phi) X + sin(phi) Y), a Hermitian involution whose Bloch vector is the unit vector with polar angle theta and azimuth phi; X, Y and Z are the Pauli matrices.

**Definition 1.2 (The binary stabilizing set).**

$$A \in \operatorname{binarySet} \Leftrightarrow ((\exists \theta \varphi, A = \operatorname{binaryOp}\left(\theta, \varphi\right)) \lor (A = 1))$$

*Formalization.* `D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.binarySet` (`✓ std3`).

*Citation.* Éloi Descamps, Borivoje Dakić (2024). *On the stabilizer formalism and its generalization*. DOI: [10.1088/1751-8121/ad8607](https://doi.org/10.1088/1751-8121/ad8607). URL: <https://arxiv.org/abs/2309.09815v1>.

*Commentary.*

The stabilizing set of the conjecture: all binary operators A(theta, phi) together with the identity.

**Definition 1.3 (The Pauli stabilizing set).**

$$A \in \operatorname{pauliSet} \Leftrightarrow (\exists c \in \{1, -1, i, -i\}, \exists p, A = c \cdot \operatorname{pauliMatrix}\left(p\right))$$

*Formalization.* `D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.pauliSet` (`✓ std3`).

*Citation.* Éloi Descamps, Borivoje Dakić (2024). *On the stabilizer formalism and its generalization*. DOI: [10.1088/1751-8121/ad8607](https://doi.org/10.1088/1751-8121/ad8607). URL: <https://arxiv.org/abs/2309.09815v1>.

*Commentary.*

The stabilizing set of the standard stabilizer formalism: the Pauli matrices 1, X, Y, Z multiplied by a phase in {1, -1, i, -i}.

**Definition 1.4 (Stabilized states).**

$$\operatorname{StabilizedBy}\left(S, \psi\right) \Leftrightarrow ((\psi \ne 0) \land (\exists k O, (\forall a i, O\left(a, i\right) \in S) \land (\forall w, (\forall a, \operatorname{tensorOp}\left(O\left(a\right)\right) w = w) \Leftrightarrow (\exists c, w = c \cdot \psi))))$$

*Formalization.* `D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.StabilizedBy` (`✓ std3`).

*Citation.* Éloi Descamps, Borivoje Dakić (2024). *On the stabilizer formalism and its generalization*. DOI: [10.1088/1751-8121/ad8607](https://doi.org/10.1088/1751-8121/ad8607). URL: <https://arxiv.org/abs/2309.09815v1>.

*Commentary.*

A nonzero state psi of N qubits is stabilized by a stabilizing set S when finitely many operators O_1, ..., O_k, each a tensor product of N elements of S, have psi as their unique common +1 eigenvector up to a complex factor. No commutativity is required.

**Definition 1.5 (Local equivalence).**

$$\operatorname{LocallyEquivalent}\left(\psi, \phi\right) \Leftrightarrow (\exists U, (\forall i, U\left(i\right) \in \operatorname{U}\left(2\right)) \land (\psi = \operatorname{tensorOp}\left(U\right) \phi))$$

*Formalization.* `D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.LocallyEquivalent` (`✓ std3`).

*Citation.* Éloi Descamps, Borivoje Dakić (2024). *On the stabilizer formalism and its generalization*. DOI: [10.1088/1751-8121/ad8607](https://doi.org/10.1088/1751-8121/ad8607). URL: <https://arxiv.org/abs/2309.09815v1>.

*Commentary.*

Two N-qubit states are locally equivalent when psi = (U_1 x ... x U_N) phi for single-qubit unitaries U_1, ..., U_N.

**Definition 1.6 (The conjecture).**

$$claim \Leftrightarrow (\forall N \psi, (\operatorname{StabilizedBy}\left(\operatorname{binarySet}, \psi\right)) \Rightarrow \exists \phi, (\operatorname{StabilizedBy}\left(\operatorname{pauliSet}, \phi\right)) \land (\operatorname{LocallyEquivalent}\left(\psi, \phi\right)))$$

*Formalization.* `D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.claim` (`✓ std3`).

*Citation.* Éloi Descamps, Borivoje Dakić (2024). *On the stabilizer formalism and its generalization*. DOI: [10.1088/1751-8121/ad8607](https://doi.org/10.1088/1751-8121/ad8607). URL: <https://arxiv.org/abs/2309.09815v1>.

*Commentary.*

The conjecture of the paper: for every number N of qubits, every state stabilized by the binary operators and the identity is locally equivalent to a state stabilized by the Pauli set.

**Theorem 1.7 (A six-qubit counterexample).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.result` (`✓ std3`). ∎

*Resolves.* `Problems/descamps-2024-binary-stabilizer-local-equivalence` (refuted) by `D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"descamps-2024-binary-stabilizer-local-equivalence","declaration_gid":"D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Éloi Descamps, Borivoje Dakić (2024). *On the stabilizer formalism and its generalization*. DOI: [10.1088/1751-8121/ad8607](https://doi.org/10.1088/1751-8121/ad8607). URL: <https://arxiv.org/abs/2309.09815v1>.

*Commentary.*

Let v be the vector with coefficient 1 on the six labels of Hamming weight one, -1 on the six labels of weight five and 0 elsewhere, and take O_1 = (-X) x X x X x X x X x X, O_2 = (-Z) x Z x Z x Z x Z x Z, O_3 = H x ... x H and O_4 = K x ... x K with H = (X + Z)/sqrt(2) and K = (X + Y)/sqrt(2), all tensor products of binary operators. The diagonal operator O_2 forces the coefficients of even weight to vanish, O_1 makes the coefficients of complementary labels opposite, O_4 then forces the weight-three coefficients to vanish, and O_3 evaluated on six weight-three labels forces the six weight-one coefficients to be equal; conversely all four fix v, so v is stabilized. For a state phi stabilized by phased Pauli words, every Pauli word P either anticommutes with some stabilizer T, and then <phi, P phi> = <T phi, P T phi> = -<phi, P phi> = 0, or commutes with all of them, and then P phi is again a common +1 eigenvector, so P phi = c phi with c = 1 or c = -1. Hence the pair purity, the sum over the sixteen words g x h x 1 x 1 x 1 x 1 of |<phi, (g x h x 1 x 1 x 1 x 1) phi>|^2, is an integer multiple of |phi|^4. The pair purity equals 4 times the squared Frobenius norm of the reduced state of qubits 1 and 2, which local unitaries conjugate by a unitary, so it is invariant under local equivalence, and so is |phi|. For v the pair purity is 192 while |v|^4 = 144, and 192 is not an integer multiple of 144.

## References

- Truth anchor: `D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.LocallyEquivalent`
- Truth anchor: `D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.StabilizedBy`
- Truth anchor: `D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.binaryOp`
- Truth anchor: `D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.binarySet`
- Truth anchor: `D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.claim`
- Truth anchor: `D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.pauliSet`
- Truth anchor: `D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.result`
- Dependency: [D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence](StabilizerPairLocalUnitaryInequivalence.md)
