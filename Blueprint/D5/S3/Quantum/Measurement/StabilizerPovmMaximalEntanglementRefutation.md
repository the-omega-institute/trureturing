# A stabilizer measurement beyond every maximally entangled one

## Abstract

A pure three-qubit ancilla separates the information dimensions of two stabilizer measurements: two Bell pairs and local Z measurements give at least 32, whereas every maximally entangled stabilizer measurement gives at most 31. This refutes Conjecture 1 of Lo Monaco et al., arXiv:2510.00157v2.

**Definition 1.1 (Computational indices).**

$$\forall n: \mathbb{N}, \operatorname{QubitIndex}\left(n\right) = (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(2\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.QubitIndex` (`✓ std3`).

*Citation.* Gabriele Lo Monaco; Salvatore Lorenzo; Alessandro Ferraro; Mauro Paternostro; G. Massimo Palma; Luca Innocenti (2025). *The non-stabilizerness cost of quantum state estimation*. DOI: [10.48550/arXiv.2510.00157](https://doi.org/10.48550/arXiv.2510.00157). URL: <https://arxiv.org/abs/2510.00157v2>.

*Commentary.*

An n-qubit computational index is a binary function on Fin n; index 0 is the first, most significant qubit.

**Definition 1.2 (State vectors).**

$$\forall n: \mathbb{N}, \operatorname{State}\left(n\right) = (\operatorname{QubitIndex}\left(n\right)) \to \mathbb{C}$$

*Formalization.* `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.State` (`✓ std3`).

*Citation.* Gabriele Lo Monaco; Salvatore Lorenzo; Alessandro Ferraro; Mauro Paternostro; G. Massimo Palma; Luca Innocenti (2025). *The non-stabilizerness cost of quantum state estimation*. DOI: [10.48550/arXiv.2510.00157](https://doi.org/10.48550/arXiv.2510.00157). URL: <https://arxiv.org/abs/2510.00157v2>.

*Commentary.*

State vectors are complex functions on the computational indices.

**Definition 1.3 (Operators).**

$$\forall n: \mathbb{N}, \operatorname{Operator}\left(n\right) = \operatorname{Matrix}\left(\operatorname{QubitIndex}\left(n\right), \operatorname{QubitIndex}\left(n\right), \mathbb{C}\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.Operator` (`✓ std3`).

*Citation.* Gabriele Lo Monaco; Salvatore Lorenzo; Alessandro Ferraro; Mauro Paternostro; G. Massimo Palma; Luca Innocenti (2025). *The non-stabilizerness cost of quantum state estimation*. DOI: [10.48550/arXiv.2510.00157](https://doi.org/10.48550/arXiv.2510.00157). URL: <https://arxiv.org/abs/2510.00157v2>.

*Commentary.*

Operators are complex matrices with computational row and column indices.

**Definition 1.4 (Pauli words).**

$$\forall n: \mathbb{N}, \operatorname{Word}\left(n\right) = (\operatorname{Fin}\left(n\right)) \to Pauli$$

*Formalization.* `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.Word` (`✓ std3`).

*Citation.* Gabriele Lo Monaco; Salvatore Lorenzo; Alessandro Ferraro; Mauro Paternostro; G. Massimo Palma; Luca Innocenti (2025). *The non-stabilizerness cost of quantum state estimation*. DOI: [10.48550/arXiv.2510.00157](https://doi.org/10.48550/arXiv.2510.00157). URL: <https://arxiv.org/abs/2510.00157v2>.

*Commentary.*

A Pauli word assigns one of the existing labels I, X, Y, Z to every qubit. Its matrix is the tensor product wordOp, with Y = i X Z.

**Definition 1.5 (Pauli phases).**

$$\forall c: \mathbb{C}, \operatorname{Phase}\left(c\right) \Leftrightarrow ((c = 1) \lor ((c = -1) \lor ((c = i) \lor (c = -i))))$$

*Formalization.* `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.Phase` (`✓ std3`).

*Citation.* Gabriele Lo Monaco; Salvatore Lorenzo; Alessandro Ferraro; Mauro Paternostro; G. Massimo Palma; Luca Innocenti (2025). *The non-stabilizerness cost of quantum state estimation*. DOI: [10.48550/arXiv.2510.00157](https://doi.org/10.48550/arXiv.2510.00157). URL: <https://arxiv.org/abs/2510.00157v2>.

*Commentary.*

The allowed scalar phases are 1, -1, i and -i; i is the imaginary unit.

**Definition 1.6 (Negative identity unit).**

$$\forall n: \mathbb{N}, \operatorname{negIdentity}\left(n\right) = \langle-\operatorname{one}\left(\operatorname{Operator}\left(n\right)\right), -\operatorname{one}\left(\operatorname{Operator}\left(n\right)\right)\rangle$$

*Formalization.* `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.negIdentity` (`✓ std3`).

*Citation.* Gabriele Lo Monaco; Salvatore Lorenzo; Alessandro Ferraro; Mauro Paternostro; G. Massimo Palma; Luca Innocenti (2025). *The non-stabilizerness cost of quantum state estimation*. DOI: [10.48550/arXiv.2510.00157](https://doi.org/10.48550/arXiv.2510.00157). URL: <https://arxiv.org/abs/2510.00157v2>.

*Commentary.*

The negative identity is a matrix unit whose value and inverse are both minus the identity matrix.

**Definition 1.7 (The Pauli group).**

$$\forall n: \mathbb{N}, \forall u: (\operatorname{Operator}\left(n\right))^{\times}, u \in \operatorname{pauliGroup}\left(n\right) \Leftrightarrow (\exists c: \mathbb{C}, (\operatorname{Phase}\left(c\right)) \land (\exists w: \operatorname{Word}\left(n\right), (\operatorname{val}\left(u\right): \operatorname{Operator}\left(n\right)) = c \cdot \operatorname{wordOp}\left(w\right)))$$

*Formalization.* `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.pauliGroup` (`✓ std3`).

*Citation.* Gabriele Lo Monaco; Salvatore Lorenzo; Alessandro Ferraro; Mauro Paternostro; G. Massimo Palma; Luca Innocenti (2025). *The non-stabilizerness cost of quantum state estimation*. DOI: [10.48550/arXiv.2510.00157](https://doi.org/10.48550/arXiv.2510.00157). URL: <https://arxiv.org/abs/2510.00157v2>.

*Commentary.*

Appendix A, PDF page 12: "The n-qubit Pauli group Pₙ is the group generated by the n-fold tensor products of the single-qubit Pauli matrices, {I, X, Y, Z}, along with multiplicative factors of ±1, ±i." The displayed membership gives the literal subgroup of matrix units, including its scalar phases.

**Definition 1.8 (Stabilizer groups).**

$$\forall n: \mathbb{N}, \operatorname{StabilizerGroup}\left(n\right) = \{S: \operatorname{Subgroup}\left((\operatorname{Operator}\left(n\right))^{\times}\right) \mid (S \le \operatorname{pauliGroup}\left(n\right)) \land ((\forall x: (\operatorname{Operator}\left(n\right))^{\times}, (x \in S) \Rightarrow \forall y: (\operatorname{Operator}\left(n\right))^{\times}, (y \in S) \Rightarrow x \cdot y = y \cdot x) \land ((\neg \operatorname{negIdentity}\left(n\right) \in S) \land (\forall T: \operatorname{Subgroup}\left((\operatorname{Operator}\left(n\right))^{\times}\right), (T \le \operatorname{pauliGroup}\left(n\right)) \Rightarrow \left((\forall x: (\operatorname{Operator}\left(n\right))^{\times}, (x \in T) \Rightarrow \forall y: (\operatorname{Operator}\left(n\right))^{\times}, (y \in T) \Rightarrow x \cdot y = y \cdot x) \Rightarrow \left((\neg \operatorname{negIdentity}\left(n\right) \in T) \Rightarrow \left((S \le T) \Rightarrow T = S\right)\right)\right))))\}$$

*Formalization.* `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.StabilizerGroup` (`✓ std3`).

*Citation.* Gabriele Lo Monaco; Salvatore Lorenzo; Alessandro Ferraro; Mauro Paternostro; G. Massimo Palma; Luca Innocenti (2025). *The non-stabilizerness cost of quantum state estimation*. DOI: [10.48550/arXiv.2510.00157](https://doi.org/10.48550/arXiv.2510.00157). URL: <https://arxiv.org/abs/2510.00157v2>.

*Commentary.*

Section II, PDF page 4: "Equivalently, a stabilizer group can be defined as a maximal Abelian subgroup of Pₙ that does not contain −I." StabilizerGroup n is the record of a subgroup S and proofs of precisely the displayed conditions. Maximality is among Abelian Pauli subgroups excluding the negative identity, not among all Abelian subgroups.

**Definition 1.9 (Rank-one projectors).**

$$\forall n: \mathbb{N}, \forall v: \operatorname{State}\left(n\right), \operatorname{projector}\left(v\right) = \operatorname{vecMulVec}\left(v, \operatorname{star}\left(v\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.projector` (`✓ std3`).

*Citation.* Gabriele Lo Monaco; Salvatore Lorenzo; Alessandro Ferraro; Mauro Paternostro; G. Massimo Palma; Luca Innocenti (2025). *The non-stabilizerness cost of quantum state estimation*. DOI: [10.48550/arXiv.2510.00157](https://doi.org/10.48550/arXiv.2510.00157). URL: <https://arxiv.org/abs/2510.00157v2>.

*Commentary.*

The projector expression is v v*, the outer product with the entrywise conjugate vector; unit vectors give orthogonal rank-one projectors.

**Definition 1.10 (Common eigenvectors).**

$$\forall n: \mathbb{N}, \forall S: \operatorname{StabilizerGroup}\left(n\right), \forall v: \operatorname{State}\left(n\right), \operatorname{CommonEigenvector}\left(S, v\right) \Leftrightarrow (\forall u: (\operatorname{Operator}\left(n\right))^{\times}, (u \in \operatorname{subgroup}\left(S\right)) \Rightarrow \exists e: \mathbb{C}, \operatorname{mulVec}\left((\operatorname{val}\left(u\right): \operatorname{Operator}\left(n\right)), v\right) = e \cdot v)$$

*Formalization.* `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.CommonEigenvector` (`✓ std3`).

*Citation.* Gabriele Lo Monaco; Salvatore Lorenzo; Alessandro Ferraro; Mauro Paternostro; G. Massimo Palma; Luca Innocenti (2025). *The non-stabilizerness cost of quantum state estimation*. DOI: [10.48550/arXiv.2510.00157](https://doi.org/10.48550/arXiv.2510.00157). URL: <https://arxiv.org/abs/2510.00157v2>.

*Commentary.*

A vector is a common eigenvector if every matrix unit of S has an eigenvalue on that vector. The definition itself allows zero vectors; the stabilizer basis record imposes orthonormality.

**Definition 1.11 (Data and ancilla index order).**

$$\forall n: \mathbb{N}, \forall m: \mathbb{N}, \forall d: \operatorname{QubitIndex}\left(n\right), \forall a: \operatorname{QubitIndex}\left(m\right), \operatorname{joinIndex}\left(d, a\right) = \operatorname{Fin.addCases}\left(d, a\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.joinIndex` (`✓ std3`).

*Citation.* Gabriele Lo Monaco; Salvatore Lorenzo; Alessandro Ferraro; Mauro Paternostro; G. Massimo Palma; Luca Innocenti (2025). *The non-stabilizerness cost of quantum state estimation*. DOI: [10.48550/arXiv.2510.00157](https://doi.org/10.48550/arXiv.2510.00157). URL: <https://arxiv.org/abs/2510.00157v2>.

*Commentary.*

Fin.addCases concatenates the data and ancilla binary indices, placing all data qubits first. In coordinates, joinIndex(d,a)(castAdd(m,i)) = d(i), and joinIndex(d,a)(natAdd(n,j)) = a(j).

**Definition 1.12 (Pure normalized ancillas).**

$$\forall m: \mathbb{N}, \operatorname{UnitState}\left(m\right) = \{\psi: \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{QubitIndex}\left(m\right)\right) \mid \Vert\psi\Vert = 1\}$$

*Formalization.* `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.UnitState` (`✓ std3`).

*Citation.* Gabriele Lo Monaco; Salvatore Lorenzo; Alessandro Ferraro; Mauro Paternostro; G. Massimo Palma; Luca Innocenti (2025). *The non-stabilizerness cost of quantum state estimation*. DOI: [10.48550/arXiv.2510.00157](https://doi.org/10.48550/arXiv.2510.00157). URL: <https://arxiv.org/abs/2510.00157v2>.

*Commentary.*

A pure ancilla is represented by a vector of Hilbert norm one. EuclideanSpace uses the sum-of-squared-moduli norm, rather than the maximum coordinate norm.

**Definition 1.13 (Compression to the data system).**

$$\forall n: \mathbb{N}, \forall m: \mathbb{N}, \forall A: \operatorname{Operator}\left(n + m\right), \forall \psi: \operatorname{UnitState}\left(m\right), \operatorname{compress}\left(A, \psi\right) = \operatorname{Matrix.of}\left(\lambda x: \operatorname{QubitIndex}\left(n\right), \lambda y: \operatorname{QubitIndex}\left(n\right), \sum_{a: \operatorname{QubitIndex}\left(m\right)} (\sum_{b: \operatorname{QubitIndex}\left(m\right)} (\operatorname{star}\left(\operatorname{val}\left(\psi\right)\left(a\right)\right) \cdot A\left(\operatorname{joinIndex}\left(x, a\right), \operatorname{joinIndex}\left(y, b\right)\right) \cdot \operatorname{val}\left(\psi\right)\left(b\right)))\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.compress` (`✓ std3`).

*Citation.* Gabriele Lo Monaco; Salvatore Lorenzo; Alessandro Ferraro; Mauro Paternostro; G. Massimo Palma; Luca Innocenti (2025). *The non-stabilizerness cost of quantum state estimation*. DOI: [10.48550/arXiv.2510.00157](https://doi.org/10.48550/arXiv.2510.00157). URL: <https://arxiv.org/abs/2510.00157v2>.

*Commentary.*

Compression is the matrix of (I tensor bra psi) A (I tensor ket psi) in the explicitly concatenated data and ancilla indices. Val denotes the vector underlying the UnitState subtype.

**Definition 1.14 (Stabilizer bases).**

$$\forall n: \mathbb{N}, \forall m: \mathbb{N}, \operatorname{StabilizerBasis}\left(n, m\right) = \{(G: \operatorname{StabilizerGroup}\left(n + m\right), v: (\operatorname{QubitIndex}\left(n + m\right)) \to \operatorname{State}\left(n + m\right)) \mid (\forall i: \operatorname{QubitIndex}\left(n + m\right), \forall j: \operatorname{QubitIndex}\left(n + m\right), \sum_{x: \operatorname{QubitIndex}\left(n + m\right)} (\operatorname{star}\left(v\left(i, x\right)\right) \cdot v\left(j, x\right)) = \operatorname{ite}\left(i = j, 1, 0\right)) \land ((\forall i: \operatorname{QubitIndex}\left(n + m\right), \operatorname{CommonEigenvector}\left(G, v\left(i\right)\right)) \land (\operatorname{span}\left(\mathbb{C}, \operatorname{range}\left(v\right)\right) = \operatorname{top}\left(\operatorname{Submodule}\left(\mathbb{C}, \operatorname{State}\left(n + m\right)\right)\right)))\}$$

*Formalization.* `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.StabilizerBasis` (`✓ std3`).

*Citation.* Gabriele Lo Monaco; Salvatore Lorenzo; Alessandro Ferraro; Mauro Paternostro; G. Massimo Palma; Luca Innocenti (2025). *The non-stabilizerness cost of quantum state estimation*. DOI: [10.48550/arXiv.2510.00157](https://doi.org/10.48550/arXiv.2510.00157). URL: <https://arxiv.org/abs/2510.00157v2>.

*Commentary.*

Section II, PDF page 4: "We will instead talk of a stabilizer basis to refer to an orthonormal basis of pure (stabilizer) states that are the common eigenvectors of some stabilizer group." The record consists of G, the vector family v, and the three displayed proof fields. Its 2^(n+m) vectors are indexed by QubitIndex(n+m).

**Definition 1.15 (Effective POVM elements).**

$$\forall n: \mathbb{N}, \forall m: \mathbb{N}, \forall \psi: \operatorname{UnitState}\left(m\right), \forall v: \operatorname{State}\left(n + m\right), \operatorname{\mu}\left(\psi, v\right) = \operatorname{compress}\left(\operatorname{projector}\left(v\right), \psi\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.mu` (`✓ std3`).

*Citation.* Gabriele Lo Monaco; Salvatore Lorenzo; Alessandro Ferraro; Mauro Paternostro; G. Massimo Palma; Luca Innocenti (2025). *The non-stabilizerness cost of quantum state estimation*. DOI: [10.48550/arXiv.2510.00157](https://doi.org/10.48550/arXiv.2510.00157). URL: <https://arxiv.org/abs/2510.00157v2>.

*Commentary.*

Section II, equation (1), PDF page 3: "μ_b = Tr_R[U† P_{Φ′_b} U (𝕀 ⊗ ρ_R)] = (I ⊗ ⟨ψ|) P_{Φ_b} (I ⊗ |ψ⟩)", with "P_{Φ_b} ≡ |Φ_b⟩⟨Φ_b|". Here v is Φ_b, the Heisenberg-evolved joint vector; the unitary is absorbed in v, and μ(psi,v) is precisely the second expression.

**Definition 1.16 (The information dimension).**

$$\forall n: \mathbb{N}, \forall m: \mathbb{N}, \forall \psi: \operatorname{UnitState}\left(m\right), \forall B: \operatorname{StabilizerBasis}\left(n, m\right), \operatorname{smu}\left(\psi, B\right) = \operatorname{finrank}\left(\mathbb{C}, \operatorname{span}\left(\mathbb{C}, \operatorname{range}\left(\lambda b: \operatorname{QubitIndex}\left(n + m\right), \operatorname{\mu}\left(\psi, \operatorname{vectors}\left(B\right)\left(b\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.smu` (`✓ std3`).

*Citation.* Gabriele Lo Monaco; Salvatore Lorenzo; Alessandro Ferraro; Mauro Paternostro; G. Massimo Palma; Luca Innocenti (2025). *The non-stabilizerness cost of quantum state estimation*. DOI: [10.48550/arXiv.2510.00157](https://doi.org/10.48550/arXiv.2510.00157). URL: <https://arxiv.org/abs/2510.00157v2>.

*Commentary.*

Section II, PDF page 3: "s_μ ≡ dim span({μ_b}_{b=1}^{n_out})". The displayed smu denotes s_μ. The dimension is the complex finrank of the linear span of the 2^(n+m) effective matrices, allowing repeated or zero effects.

**Definition 1.17 (Support in a set of qubits).**

$$\forall n: \mathbb{N}, \forall J: \operatorname{Set}\left(\operatorname{Fin}\left(n\right)\right), \forall u: (\operatorname{Operator}\left(n\right))^{\times}, u \in \operatorname{supportedPauliGroup}\left(n, J\right) \Leftrightarrow (\exists c: \mathbb{C}, (\operatorname{Phase}\left(c\right)) \land (\exists w: \operatorname{Word}\left(n\right), ((\operatorname{val}\left(u\right): \operatorname{Operator}\left(n\right)) = c \cdot \operatorname{wordOp}\left(w\right)) \land (\forall i: \operatorname{Fin}\left(n\right), (\neg i \in J) \Rightarrow w\left(i\right) = \operatorname{Pauli.I})))$$

*Formalization.* `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.supportedPauliGroup` (`✓ std3`).

*Citation.* Gabriele Lo Monaco; Salvatore Lorenzo; Alessandro Ferraro; Mauro Paternostro; G. Massimo Palma; Luca Innocenti (2025). *The non-stabilizerness cost of quantum state estimation*. DOI: [10.48550/arXiv.2510.00157](https://doi.org/10.48550/arXiv.2510.00157). URL: <https://arxiv.org/abs/2510.00157v2>.

*Commentary.*

A phased Pauli word is supported in J exactly when every letter outside J is I. Support ignores the scalar phase and is defined by this literal subgroup of matrix units.

**Definition 1.18 (Support only on the data qubits).**

$$\forall n: \mathbb{N}, \forall m: \mathbb{N}, \forall S: \operatorname{StabilizerGroup}\left(n + m\right), \operatorname{dataSubgroup}\left(S\right) = \operatorname{inf}\left(\operatorname{subgroup}\left(S\right), \operatorname{supportedPauliGroup}\left(n + m, \{i: \operatorname{Fin}\left(n + m\right) \mid \operatorname{val}\left(i\right) < n\}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.dataSubgroup` (`✓ std3`).

*Citation.* Gabriele Lo Monaco; Salvatore Lorenzo; Alessandro Ferraro; Mauro Paternostro; G. Massimo Palma; Luca Innocenti (2025). *The non-stabilizerness cost of quantum state estimation*. DOI: [10.48550/arXiv.2510.00157](https://doi.org/10.48550/arXiv.2510.00157). URL: <https://arxiv.org/abs/2510.00157v2>.

*Commentary.*

Section IV, PDF page 7: "Sₙ, Sₘ ≤ S the subgroups of operators with support only on Hₙ and Hₘ, respectively". Sₙ is the intersection of S with the Pauli subgroup supported in positions whose natural index is less than n.

**Definition 1.19 (Support only on the ancilla qubits).**

$$\forall n: \mathbb{N}, \forall m: \mathbb{N}, \forall S: \operatorname{StabilizerGroup}\left(n + m\right), \operatorname{ancillaSubgroup}\left(S\right) = \operatorname{inf}\left(\operatorname{subgroup}\left(S\right), \operatorname{supportedPauliGroup}\left(n + m, \{i: \operatorname{Fin}\left(n + m\right) \mid n \le \operatorname{val}\left(i\right)\}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.ancillaSubgroup` (`✓ std3`).

*Citation.* Gabriele Lo Monaco; Salvatore Lorenzo; Alessandro Ferraro; Mauro Paternostro; G. Massimo Palma; Luca Innocenti (2025). *The non-stabilizerness cost of quantum state estimation*. DOI: [10.48550/arXiv.2510.00157](https://doi.org/10.48550/arXiv.2510.00157). URL: <https://arxiv.org/abs/2510.00157v2>.

*Commentary.*

Section IV, PDF page 7: "Sₙ, Sₘ ≤ S the subgroups of operators with support only on Hₙ and Hₘ, respectively". Sₘ is the intersection with the Pauli subgroup supported in positions whose natural index is at least n.

**Definition 1.20 (Binary dimension of the data subgroup).**

$$\forall n: \mathbb{N}, \forall m: \mathbb{N}, \forall S: \operatorname{StabilizerGroup}\left(n + m\right), \operatorname{dimData}\left(S\right) = \operatorname{Nat.log}\left(2, \operatorname{Nat.card}\left(\operatorname{dataSubgroup}\left(S\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.dimData` (`✓ std3`).

*Citation.* Gabriele Lo Monaco; Salvatore Lorenzo; Alessandro Ferraro; Mauro Paternostro; G. Massimo Palma; Luca Innocenti (2025). *The non-stabilizerness cost of quantum state estimation*. DOI: [10.48550/arXiv.2510.00157](https://doi.org/10.48550/arXiv.2510.00157). URL: <https://arxiv.org/abs/2510.00157v2>.

*Commentary.*

The F₂-dimension of the finite elementary Abelian support subgroup is the base-two natural logarithm of its cardinality. Nat.log is the floor logarithm; on these power-of-two subgroup orders it is the exact binary dimension.

**Definition 1.21 (Binary dimension of the ancilla subgroup).**

$$\forall n: \mathbb{N}, \forall m: \mathbb{N}, \forall S: \operatorname{StabilizerGroup}\left(n + m\right), \operatorname{dimAncilla}\left(S\right) = \operatorname{Nat.log}\left(2, \operatorname{Nat.card}\left(\operatorname{ancillaSubgroup}\left(S\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.dimAncilla` (`✓ std3`).

*Citation.* Gabriele Lo Monaco; Salvatore Lorenzo; Alessandro Ferraro; Mauro Paternostro; G. Massimo Palma; Luca Innocenti (2025). *The non-stabilizerness cost of quantum state estimation*. DOI: [10.48550/arXiv.2510.00157](https://doi.org/10.48550/arXiv.2510.00157). URL: <https://arxiv.org/abs/2510.00157v2>.

*Commentary.*

The ancilla support subgroup uses the same base-two natural logarithm convention.

**Definition 1.22 (Entanglement parameter).**

$$\forall n: \mathbb{N}, \forall m: \mathbb{N}, \forall S: \operatorname{StabilizerGroup}\left(n + m\right), \operatorname{entanglementP}\left(S\right) = \frac{(\operatorname{Nat.cast}\left(n\right): \mathbb{Q}) + (\operatorname{Nat.cast}\left(m\right): \mathbb{Q}) - (\operatorname{Nat.cast}\left(\operatorname{dimData}\left(S\right)\right): \mathbb{Q}) - (\operatorname{Nat.cast}\left(\operatorname{dimAncilla}\left(S\right)\right): \mathbb{Q})}{2}$$

*Formalization.* `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.entanglementP` (`✓ std3`).

*Citation.* Gabriele Lo Monaco; Salvatore Lorenzo; Alessandro Ferraro; Mauro Paternostro; G. Massimo Palma; Luca Innocenti (2025). *The non-stabilizerness cost of quantum state estimation*. DOI: [10.48550/arXiv.2510.00157](https://doi.org/10.48550/arXiv.2510.00157). URL: <https://arxiv.org/abs/2510.00157v2>.

*Commentary.*

Section IV, PDF page 7: "The parameter p quantifies the entanglement of the states and satisfies 2p = n + m − dim(Sₙ) − dim(Sₘ) and 0 ≤ p ≤ min(n, m)." The definition uses rational arithmetic for the half-difference; each natural dimension is explicitly cast to Q.

**Definition 1.23 (Maximal entanglement).**

$$\forall n: \mathbb{N}, \forall m: \mathbb{N}, \forall B: \operatorname{StabilizerBasis}\left(n, m\right), \operatorname{MaximallyEntangled}\left(B\right) \Leftrightarrow (\operatorname{entanglementP}\left(\operatorname{group}\left(B\right)\right) = (\operatorname{Nat.cast}\left(\operatorname{min}\left(n, m\right)\right): \mathbb{Q}))$$

*Formalization.* `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.MaximallyEntangled` (`✓ std3`).

*Citation.* Gabriele Lo Monaco; Salvatore Lorenzo; Alessandro Ferraro; Mauro Paternostro; G. Massimo Palma; Luca Innocenti (2025). *The non-stabilizerness cost of quantum state estimation*. DOI: [10.48550/arXiv.2510.00157](https://doi.org/10.48550/arXiv.2510.00157). URL: <https://arxiv.org/abs/2510.00157v2>.

*Commentary.*

Section IV, PDF page 7: "States are separable for p = 0 and maximally entangled for p = min(n, m)." The basis is maximally entangled exactly when its group's rational parameter equals the natural minimum, cast to Q.

**Definition 1.24 (Conjecture 1).**

$$claim \Leftrightarrow (\forall n: \mathbb{N}, \forall m: \mathbb{N}, \forall \psi: \operatorname{UnitState}\left(m\right), \exists B: \operatorname{StabilizerBasis}\left(n, m\right), (\operatorname{MaximallyEntangled}\left(B\right)) \land (\forall B': \operatorname{StabilizerBasis}\left(n, m\right), \operatorname{smu}\left(\psi, B'\right) \le \operatorname{smu}\left(\psi, B\right)))$$

*Formalization.* `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.claim` (`✓ std3`).

*Citation.* Gabriele Lo Monaco; Salvatore Lorenzo; Alessandro Ferraro; Mauro Paternostro; G. Massimo Palma; Luca Innocenti (2025). *The non-stabilizerness cost of quantum state estimation*. DOI: [10.48550/arXiv.2510.00157](https://doi.org/10.48550/arXiv.2510.00157). URL: <https://arxiv.org/abs/2510.00157v2>.

*Commentary.*

Conjecture 1, Section IV, PDF page 8: "For any pure |ψ⟩, the maximal value of s_μ can be obtained with maximally entangled S." The encoding fixes n data qubits, m ancillas and a unit vector psi, and asks for a maximally entangled stabilizer basis B whose information dimension dominates that of every stabilizer basis B′ for the same psi.

**Theorem 1.25 (A pure-state refutation).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/lo-monaco-2025-stabilizer-povm-maximal-entanglement-refutation` (refuted) by `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lo-monaco-2025-stabilizer-povm-maximal-entanglement-refutation","declaration_gid":"D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Gabriele Lo Monaco; Salvatore Lorenzo; Alessandro Ferraro; Mauro Paternostro; G. Massimo Palma; Luca Innocenti (2025). *The non-stabilizerness cost of quantum state estimation*. DOI: [10.48550/arXiv.2510.00157](https://doi.org/10.48550/arXiv.2510.00157). URL: <https://arxiv.org/abs/2510.00157v2>.

*Commentary.*

For n = m = 3 take psi = (1-i, 1+i, -2, -2, 2, 2, 2+2i, 2-2i)/6 in computational order 000 through 111. Its squared norm is one. Among the 64 three-qubit Pauli words, exactly 31 have nonzero expectations. Pauli trace orthogonality and stabilizer maximality put every basis projector in the stabilizer-group span. Maximal entanglement makes the ancilla-word projection injective, so every such basis has s_mu at most 31. For the group generated by X_0 X_3, Z_0 Z_3, X_1 X_4, Z_1 Z_4, Z_2, Z_5, take two Bell transforms and the identity on the third pair. Their columns form an orthonormal common eigenbasis of a maximal stabilizer group. For each two-qubit Pauli word P, at least one expectation of P tensor I or P tensor Z is nonzero. The 32 independent data words P tensor I and P tensor Z therefore lie in its effective span, giving s_mu at least 32. Since 32 > 31, no maximally entangled basis attains the optimum for this pure ancilla.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.CommonEigenvector`
- Truth anchor: `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.MaximallyEntangled`
- Truth anchor: `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.Operator`
- Truth anchor: `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.Phase`
- Truth anchor: `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.QubitIndex`
- Truth anchor: `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.StabilizerBasis`
- Truth anchor: `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.StabilizerGroup`
- Truth anchor: `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.State`
- Truth anchor: `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.UnitState`
- Truth anchor: `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.Word`
- Truth anchor: `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.ancillaSubgroup`
- Truth anchor: `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.compress`
- Truth anchor: `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.dataSubgroup`
- Truth anchor: `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.dimAncilla`
- Truth anchor: `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.dimData`
- Truth anchor: `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.entanglementP`
- Truth anchor: `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.joinIndex`
- Truth anchor: `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.mu`
- Truth anchor: `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.negIdentity`
- Truth anchor: `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.pauliGroup`
- Truth anchor: `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.projector`
- Truth anchor: `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.result`
- Truth anchor: `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.smu`
- Truth anchor: `D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.supportedPauliGroup`
- Dependency: [D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence](../Information/StabilizerPairLocalUnitaryInequivalence.md)
