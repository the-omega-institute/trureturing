# Three-qubit stabilizer polar elements

## Abstract

Seven anticommuting Pauli operators give positive three-qubit polar elements whose tensor product exceeds one on a stabilizer state.

**Definition 1.1 (Computational basis indices).**

$$\forall n \in \mathbb{N},\; \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Bits}\left(n\right) = \left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.Bits` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An n-qubit computational basis index assigns a bit in Fin 2 to every coordinate in Fin n.

**Definition 1.2 (Complex operators).**

$$\forall n \in \mathbb{N},\; \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(n\right) = \operatorname{D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.Operator}\left(n\right)$$

*Formalization.* `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.Op` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Op refers to D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.Operator: complex square matrices indexed by the computational basis.

**Definition 1.3 (Density matrices).**

$$\forall n \in \mathbb{N},\; \forall rho \in \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(n\right),\; (\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.IsState}\left(rho\right)) \Leftrightarrow (\operatorname{D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity}\left(rho\right))$$

*Formalization.* `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.IsState` (`✓ std3`).

*Citation.* Roberto Rubboli, Ryuji Takagi, Marco Tomamichel (2024). *Mixed-state additivity properties of magic monotones based on quantum relative entropies for single-qubit states and beyond*. DOI: [10.22331/q-2024-10-04-1492](https://doi.org/10.22331/q-2024-10-04-1492). URL: <https://arxiv.org/abs/2307.08258v4>.

*Commentary.*

IsState refers to D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity: positive semidefiniteness and complex trace one, as in §2.

**Definition 1.4 (Real part of the trace).**

$$\forall n \in \mathbb{N},\; \forall A \in \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(n\right),\; \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.tr}\left(A\right) = \operatorname{RHLinalg.rtrace}\left(A\right)$$

*Formalization.* `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.tr` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real-valued trace refers to RHLinalg.rtrace, the real part of Matrix.trace. It is defined for every operator.

**Definition 1.5 (Entrywise complex conjugation).**

$$\forall n \in \mathbb{N},\; \forall A \in \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(n\right),\; \forall x \in \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Bits}\left(n\right),\; \forall y \in \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Bits}\left(n\right),\; \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.conjugate}\left(A\right)\left(x, y\right) = \operatorname{star}\left(A\left(x, y\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.conjugate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Conjugation applies star to each complex entry without exchanging the row and column indices.

**Definition 1.6 (Tensor products in bit coordinates).**

$$\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall A \in \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(n\right),\; \forall B \in \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(m\right),\; \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.tensor}\left(A, B\right) = \operatorname{Matrix.submatrix}\left(\operatorname{Matrix.kronecker}\left(A, B\right), (\lambda (x: \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Bits}\left(n + m\right)) \mapsto (((\lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (x\left(\operatorname{Fin.castAdd}\left(m, i\right)\right))), (\lambda (j: \operatorname{Fin}\left(m\right)) \mapsto (x\left(\operatorname{Fin.natAdd}\left(n, j\right)\right)))))), (\lambda (x: \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Bits}\left(n + m\right)) \mapsto (((\lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (x\left(\operatorname{Fin.castAdd}\left(m, i\right)\right))), (\lambda (j: \operatorname{Fin}\left(m\right)) \mapsto (x\left(\operatorname{Fin.natAdd}\left(n, j\right)\right))))))\right)$$

*Formalization.* `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.tensor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Matrix.kronecker initially uses pairs of basis indices. Matrix.submatrix reindexes both rows and columns by restriction to the first n and last m bits, using Fin.castAdd and Fin.natAdd respectively.

**Definition 1.7 (The Hadamard gate).**

$$\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.gateH} = \operatorname{D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.hadamard}$$

*Formalization.* `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.gateH` (`✓ std3`).

*Citation.* Roberto Rubboli, Ryuji Takagi, Marco Tomamichel (2024). *Mixed-state additivity properties of magic monotones based on quantum relative entropies for single-qubit states and beyond*. DOI: [10.22331/q-2024-10-04-1492](https://doi.org/10.22331/q-2024-10-04-1492). URL: <https://arxiv.org/abs/2307.08258v4>.

*Commentary.*

The Hadamard gate is the matrix D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.hadamard. It is one of the Clifford generators in §2.

**Definition 1.8 (The phase gate).**

$$\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.gateS} = \operatorname{Matrix.diagonal}\left(![(1: \mathbb{C}), \operatorname{Complex.I}]\right)$$

*Formalization.* `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.gateS` (`✓ std3`).

*Citation.* Roberto Rubboli, Ryuji Takagi, Marco Tomamichel (2024). *Mixed-state additivity properties of magic monotones based on quantum relative entropies for single-qubit states and beyond*. DOI: [10.22331/q-2024-10-04-1492](https://doi.org/10.22331/q-2024-10-04-1492). URL: <https://arxiv.org/abs/2307.08258v4>.

*Commentary.*

The phase gate is diagonal with entries 1 and Complex.I, the single-qubit phase gate of §2.

**Definition 1.9 (Controlled addition of a bit).**

$$\forall n \in \mathbb{N},\; \forall c \in \operatorname{Fin}\left(n\right),\; \forall t \in \operatorname{Fin}\left(n\right),\; \forall x \in \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Bits}\left(n\right),\; \forall y \in \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Bits}\left(n\right),\; \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.gateCNOT}\left(c, t\right)\left(x, y\right) = \operatorname{ite}\left(x = \operatorname{Function.update}\left(y, t, y\left(t\right) + y\left(c\right)\right), (1: \mathbb{C}), (0: \mathbb{C})\right)$$

*Formalization.* `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.gateCNOT` (`✓ std3`).

*Citation.* Roberto Rubboli, Ryuji Takagi, Marco Tomamichel (2024). *Mixed-state additivity properties of magic monotones based on quantum relative entropies for single-qubit states and beyond*. DOI: [10.22331/q-2024-10-04-1492](https://doi.org/10.22331/q-2024-10-04-1492). URL: <https://arxiv.org/abs/2307.08258v4>.

*Commentary.*

The target bit is replaced by its sum with the control bit in Fin 2. The matrix entry is one exactly when this update sends the column index to the row index. Distinct control and target coordinates are required when choosing generators, as in §2.

**Definition 1.10 (The generating gates).**

$$\forall n \in \mathbb{N},\; \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.gates}\left(n\right) = \{(U: \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(n\right)) \mid (\exists i \in \operatorname{Fin}\left(n\right),\; U = \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp}\left(i, \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.gateH}\right)) \lor ((\exists i \in \operatorname{Fin}\left(n\right),\; U = \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp}\left(i, \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.gateS}\right)) \lor (\exists c \in \operatorname{Fin}\left(n\right),\; \exists t \in \operatorname{Fin}\left(n\right),\; (c \ne t) \land (U = \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.gateCNOT}\left(c, t\right))))\}$$

*Formalization.* `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.gates` (`✓ std3`).

*Citation.* Roberto Rubboli, Ryuji Takagi, Marco Tomamichel (2024). *Mixed-state additivity properties of magic monotones based on quantum relative entropies for single-qubit states and beyond*. DOI: [10.22331/q-2024-10-04-1492](https://doi.org/10.22331/q-2024-10-04-1492). URL: <https://arxiv.org/abs/2307.08258v4>.

*Commentary.*

The generating set consists of local Hadamard gates, local phase gates, and controlled-not gates with distinct control and target coordinates, as in §2.

**Definition 1.11 (The generated Clifford submonoid).**

$$\forall n \in \mathbb{N},\; \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Clifford}\left(n\right) = \operatorname{Submonoid.closure}\left(\operatorname{Set.union}\left(\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.gates}\left(n\right), \operatorname{Set.image}\left((\lambda (U: \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(n\right)) \mapsto (\operatorname{Matrix.conjTranspose}\left(U\right))), \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.gates}\left(n\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.Clifford` (`✓ std3`).

*Citation.* Roberto Rubboli, Ryuji Takagi, Marco Tomamichel (2024). *Mixed-state additivity properties of magic monotones based on quantum relative entropies for single-qubit states and beyond*. DOI: [10.22331/q-2024-10-04-1492](https://doi.org/10.22331/q-2024-10-04-1492). URL: <https://arxiv.org/abs/2307.08258v4>.

*Commentary.*

Section 2 defines the Clifford group by the Hadamard, phase and controlled-not generators. Here Submonoid.closure includes the generators and their conjugate transposes; it is a submonoid of the matrix monoid.

**Definition 1.12 (The zero-bit projector).**

$$\forall n \in \mathbb{N},\; \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.vacuum}\left(n\right) = \operatorname{Matrix.single}\left(\operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin.castSucc}\left(\operatorname{Fin.last}\left(0\right)\right)\right), \operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin.castSucc}\left(\operatorname{Fin.last}\left(0\right)\right)\right), (1: \mathbb{C})\right)$$

*Formalization.* `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.vacuum` (`✓ std3`).

*Citation.* Roberto Rubboli, Ryuji Takagi, Marco Tomamichel (2024). *Mixed-state additivity properties of magic monotones based on quantum relative entropies for single-qubit states and beyond*. DOI: [10.22331/q-2024-10-04-1492](https://doi.org/10.22331/q-2024-10-04-1492). URL: <https://arxiv.org/abs/2307.08258v4>.

*Commentary.*

Matrix.single gives the projector onto the all-zero computational basis vector used in §2. Fin.castSucc (Fin.last 0) is the zero element of Fin 2.

**Definition 1.13 (Pure stabilizer projectors).**

$$\forall n \in \mathbb{N},\; \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.PureStabilizer}\left(n\right) = \{(rho: \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(n\right)) \mid \exists U \in \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(n\right),\; (U \in \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Clifford}\left(n\right)) \land (rho = U \cdot \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.vacuum}\left(n\right) \cdot \operatorname{Matrix.conjTranspose}\left(U\right))\}$$

*Formalization.* `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.PureStabilizer` (`✓ std3`).

*Citation.* Roberto Rubboli, Ryuji Takagi, Marco Tomamichel (2024). *Mixed-state additivity properties of magic monotones based on quantum relative entropies for single-qubit states and beyond*. DOI: [10.22331/q-2024-10-04-1492](https://doi.org/10.22331/q-2024-10-04-1492). URL: <https://arxiv.org/abs/2307.08258v4>.

*Commentary.*

The pure stabilizer projectors of §2 are conjugates of the zero-bit projector by elements of the Clifford submonoid.

**Definition 1.14 (Mixed stabilizer states).**

$$\forall n \in \mathbb{N},\; \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.STAB}\left(n\right) = \operatorname{convexHull}\left(\mathbb{R}, \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.PureStabilizer}\left(n\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.STAB` (`✓ std3`).

*Citation.* Roberto Rubboli, Ryuji Takagi, Marco Tomamichel (2024). *Mixed-state additivity properties of magic monotones based on quantum relative entropies for single-qubit states and beyond*. DOI: [10.22331/q-2024-10-04-1492](https://doi.org/10.22331/q-2024-10-04-1492). URL: <https://arxiv.org/abs/2307.08258v4>.

*Commentary.*

The mixed stabilizer states in §2 form the convex hull over the real numbers of the pure stabilizer projectors.

**Definition 1.15 (The seven Pauli words).**

$$\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.gammaWords} = ![![\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.X}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.I}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.I}], ![\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Y}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.I}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.I}], ![\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Z}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.X}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.I}], ![\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Z}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Y}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.I}], ![\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Z}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Z}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.X}], ![\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Z}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Z}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Y}], ![\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Z}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Z}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Z}]]$$

*Formalization.* `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.gammaWords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The seven three-qubit words are XII, YII, ZXI, ZYI, ZZX, ZZY and ZZZ.

**Theorem 1.16 (Adjoints of local gates).**

$$\forall n \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{Matrix.conjTranspose}\left(\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp}\left(i, A\right)\right) = \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp}\left(i, \operatorname{Matrix.conjTranspose}\left(A\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.local_adjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking the adjoint commutes with embedding a single-qubit operator at a fixed coordinate.

**Theorem 1.17 (Local gates preserve products).**

$$\forall n \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp}\left(i, A\right) \cdot \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp}\left(i, B\right) = \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp}\left(i, A \cdot B\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.local_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Embedding two single-qubit operators at the same coordinate preserves their product.

**Theorem 1.18 (The local identity gate).**

$$\forall n \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp}\left(i, (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))\right) = (1: \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.local_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Embedding the single-qubit identity at any coordinate gives the identity on the full register.

**Definition 1.19 (Seven anticommuting Pauli terms).**

$$\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.S} = \sum_{(j: \operatorname{Fin}\left(7\right))} (\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.wordOp}\left(![![\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.X}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.I}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.I}], ![\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Y}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.I}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.I}], ![\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Z}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.X}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.I}], ![\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Z}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Y}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.I}], ![\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Z}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Z}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.X}], ![\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Z}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Z}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Y}], ![\operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Z}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Z}, \operatorname{D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Z}]]\left(j\right)\right))$$

*Formalization.* `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.S` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The seven words are XII, YII, ZXI, ZYI, ZZX, ZZY and ZZZ. Their Pauli operators anticommute pairwise, so the cross terms in the square cancel.

**Definition 1.20 (A three-qubit state).**

$$\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.sigma} = ((\frac{1}{56}: \mathbb{R})) \cdot (((7: \mathbb{R})) \cdot ((1: \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(3\right))) + \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.S})$$

*Formalization.* `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.sigma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This state is one seventh of the sum of the seven states obtained from the identity plus each Pauli term, divided by eight. Its expectation of S is one.

**Definition 1.21 (Three Bell pairs).**

$$\forall x \in \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Bits}\left(6\right),\; \forall y \in \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Bits}\left(6\right),\; \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.bell}\left(x, y\right) = \operatorname{ite}\left(((\lambda (i: \operatorname{Fin}\left(3\right)) \mapsto (x\left(\operatorname{Fin.castAdd}\left(3, i\right)\right))) = (\lambda (i: \operatorname{Fin}\left(3\right)) \mapsto (x\left(\operatorname{Fin.natAdd}\left(3, i\right)\right)))) \land ((\lambda (i: \operatorname{Fin}\left(3\right)) \mapsto (y\left(\operatorname{Fin.castAdd}\left(3, i\right)\right))) = (\lambda (i: \operatorname{Fin}\left(3\right)) \mapsto (y\left(\operatorname{Fin.natAdd}\left(3, i\right)\right)))), (\frac{1}{8}: \mathbb{C}), (0: \mathbb{C})\right)$$

*Formalization.* `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.bell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The projector has entry 1/8 when the two three-bit halves of each basis index coincide, and zero otherwise. It is the maximally entangled state between the two three-qubit factors.

**Definition 1.22 (Positive polar elements).**

$$\forall s \in \mathbb{R},\; \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.W}\left(s\right) = ((\frac{1}{1 + s}: \mathbb{R})) \cdot ((1: \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(3\right)) + (s) \cdot (\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.S}))$$

*Formalization.* `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.W` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the parameter range in the theorem, this operator and its entrywise conjugate are positive definite and have expectation at most one on every three-qubit stabilizer state.

**Theorem 1.23 (The tensor product exceeds the polar bound).**

$$\forall s \in \mathbb{R},\; (\frac{1}{3} < s) \Rightarrow ((7 \cdot (s)^{2} < 1) \Rightarrow ((\forall n \in \mathbb{N},\; \forall eta \in \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(n\right),\; (eta \in \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.STAB}\left(n\right)) \Rightarrow (\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.IsState}\left(eta\right))) \land (((\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.IsState}\left(\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.sigma}\right)) \land (\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.tr}\left(\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.sigma} \cdot \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.S}\right) = 1)) \land ((\operatorname{Matrix.conjTranspose}\left(\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.S}\right) = \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.S}) \land ((\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.S} \cdot \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.S} = ((7: \mathbb{C})) \cdot ((1: \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(3\right)))) \land ((\operatorname{Matrix.trace}\left(\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.S}\right) = (0: \mathbb{C})) \land ((\forall A \in \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(3\right),\; \forall B \in \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(3\right),\; \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.tr}\left(\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.bell} \cdot \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.tensor}\left(A, \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.conjugate}\left(B\right)\right)\right) = \frac{\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.tr}\left(A \cdot \operatorname{Matrix.conjTranspose}\left(B\right)\right)}{8}) \land ((\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.bell} \in \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.STAB}\left(6\right)) \land ((\operatorname{Matrix.PosDef}\left(\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.W}\left(s\right)\right)) \land ((\operatorname{Matrix.PosDef}\left(\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.conjugate}\left(\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.W}\left(s\right)\right)\right)) \land ((\forall eta \in \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(3\right),\; (eta \in \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.STAB}\left(3\right)) \Rightarrow ((\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.tr}\left(eta \cdot \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.W}\left(s\right)\right) \le 1) \land (\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.tr}\left(eta \cdot \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.conjugate}\left(\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.W}\left(s\right)\right)\right) \le 1))) \land ((\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.tr}\left(\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.bell} \cdot \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.tensor}\left(\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.W}\left(s\right), \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.conjugate}\left(\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.W}\left(s\right)\right)\right)\right) = \frac{1 + 7 \cdot (s)^{2}}{(1 + s)^{2}}) \land (1 < \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.tr}\left(\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.bell} \cdot \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.tensor}\left(\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.W}\left(s\right), \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.conjugate}\left(\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.W}\left(s\right)\right)\right)\right))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.stabilizer_polar_tensor_escape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 1/3 < s and 7s² < 1, the two positive definite three-qubit operators each have expectation at most one on STAB 3. Their tensor product has expectation (1 + 7s²)/(1 + s)², strictly greater than one, on the six-qubit stabilizer state of three Bell pairs. The same statement supplies the state property of every stabilizer mixture, the expectation of S in sigma, the adjoint, square and trace of S, and the trace pairing for arbitrary three-qubit operators.

## References

- Truth anchor: `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.Bits`
- Truth anchor: `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.Clifford`
- Truth anchor: `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.IsState`
- Truth anchor: `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.Op`
- Truth anchor: `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.PureStabilizer`
- Truth anchor: `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.S`
- Truth anchor: `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.STAB`
- Truth anchor: `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.W`
- Truth anchor: `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.bell`
- Truth anchor: `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.conjugate`
- Truth anchor: `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.gammaWords`
- Truth anchor: `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.gateCNOT`
- Truth anchor: `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.gateH`
- Truth anchor: `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.gateS`
- Truth anchor: `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.gates`
- Truth anchor: `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.local_adjoint`
- Truth anchor: `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.local_identity`
- Truth anchor: `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.local_product`
- Truth anchor: `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.sigma`
- Truth anchor: `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.stabilizer_polar_tensor_escape`
- Truth anchor: `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.tensor`
- Truth anchor: `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.tr`
- Truth anchor: `D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.vacuum`
- Dependency: [D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound](../Entanglement/GHZMeasureBiseparableBound.md)
- Dependency: [D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation](../Entanglement/NandiMutualPredictabilityLOCCRefutation.md)
- Dependency: [D5/S3/Quantum/Fibers/PhysicalFiber](../Fibers/PhysicalFiber.md)
- Dependency: [D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm](../Information/BinaryStabilizerGraphNormalForm.md)
- Dependency: [D5/S3/Quantum/Information/SLDSpectralEnergy](../Information/SLDSpectralEnergy.md)
- Dependency: [D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation](../Measurement/StabilizerPovmMaximalEntanglementRefutation.md)
- Dependency: [D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations](../Measurements/CliffordJointMeasurability/CliffordPathRealizations.md)
