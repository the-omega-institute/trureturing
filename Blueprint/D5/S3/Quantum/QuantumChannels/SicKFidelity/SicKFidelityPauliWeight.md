# Pauli-weight expansion and alternating truncation bounds for qubit SIC k-fidelities

## Abstract

Multi-qubit Pauli process matrices, Pauli-twirl weight distributions, single-qubit SIC projectors and overlap-inverse kernels, per-qubit diagonal functionals, the alternating binomial Pauli-weight formula for every SIC k-fidelity of an arbitrary linear qubit map, and alternating truncation bounds for completely positive maps.

**Definition 1.1 (Computational basis index).**

$$\forall n \in \mathbb{N},\; \operatorname{QubitIndex}\left(n\right) = \left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.QubitIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

For n qubits, QubitIndex(n) is the function type Fin n -> Fin 2 indexing the 2^n computational basis vectors.

**Definition 1.2 (Multi-qubit Pauli string label).**

$$\forall n \in \mathbb{N},\; \operatorname{PauliLabel}\left(n\right) = \left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(4\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.PauliLabel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

For n qubits, PauliLabel(n) is the function type Fin n -> Fin 4 indexing the 4^n tensor-product Pauli strings.

**Definition 1.3 (Linear superoperator on n qubits).**

$$\forall n \in \mathbb{N},\; \operatorname{QubitMap}\left(n\right) = \operatorname{MatrixMap}\left(\operatorname{QubitIndex}\left(n\right), \operatorname{QubitIndex}\left(n\right), \mathbb{C}\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.QubitMap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

For n qubits, QubitMap(n) is the space of complex-linear maps on 2^n by 2^n complex matrices.

**Definition 1.4 (Single-qubit Pauli matrices).**

$$\operatorname{pauli1}\left(0\right) = 1 \land \left(\operatorname{pauli1}\left(1\right) = \operatorname{qubitX} \land \left(\operatorname{pauli1}\left(2\right) = \begin{pmatrix}0 & -\operatorname{I} \\ \operatorname{I} & 0\end{pmatrix} \land \operatorname{pauli1}\left(3\right) = \operatorname{qubitZ}\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.pauli1` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Maps 0, 1, 2, 3 in Fin 4 to the 2 by 2 complex matrices I, X, Y, Z.

**Definition 1.5 (Tensor-product Pauli operator).**

$$\forall n \in \mathbb{N},\; \forall b \in \operatorname{PauliLabel}\left(n\right),\; \forall x \in \operatorname{QubitIndex}\left(n\right),\; \forall y \in \operatorname{QubitIndex}\left(n\right),\; \operatorname{pauliN}\left(n, b\right)\left(x, y\right) = \prod_{i \in \operatorname{Fin}\left(n\right)} \operatorname{pauli1}\left(b\left(i\right)\right)\left(x\left(i\right), y\left(i\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.pauliN` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

For a multi-qubit label beta in PauliLabel(n), pauliN(n, beta) is the n-fold tensor-product matrix whose (x, y) entry is the product over i in Fin n of pauli1(beta(i))(x(i), y(i)).

**Definition 1.6 (Pauli Hamming weight).**

$$\forall n \in \mathbb{N},\; \forall b \in \operatorname{PauliLabel}\left(n\right),\; \operatorname{hammingWeight}\left(b\right) = \operatorname{card}\left(\left\{i \in \operatorname{Fin}\left(n\right) \mid b\left(i\right) \ne 0\right\}\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.hammingWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Counts the number of qubit positions i in Fin n at which beta(i) is nonzero.

**Definition 1.7 (Pauli process-matrix coefficients).**

$$\forall n \in \mathbb{N},\; \forall L \in \operatorname{QubitMap}\left(n\right),\; \forall b \in \operatorname{PauliLabel}\left(n\right),\; \forall g \in \operatorname{PauliLabel}\left(n\right),\; \operatorname{processMatrix}\left(L, b, g\right) = \left(4^{n}\right)^{-1} \cdot \sum_{u \in \operatorname{QubitIndex}\left(n\right)} \sum_{x \in \operatorname{QubitIndex}\left(n\right)} \sum_{v \in \operatorname{QubitIndex}\left(n\right)} \sum_{y \in \operatorname{QubitIndex}\left(n\right)} \operatorname{pauliN}\left(n, b\right)\left(x, u\right) \cdot L\left(\operatorname{single}\left(x, y, 1\right)\right)\left(u, v\right) \cdot \operatorname{pauliN}\left(n, g\right)\left(v, y\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.processMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Gives the unique expansion coefficient chi_{beta, gamma} of an n-qubit linear map Lambda in the basis X |-> P_beta X P_gamma by Hilbert-Schmidt contraction scaled by 4^{-n}.

**Definition 1.8 (Diagonal Pauli-twirl weight).**

$$\forall n \in \mathbb{N},\; \forall L \in \operatorname{QubitMap}\left(n\right),\; \forall b \in \operatorname{PauliLabel}\left(n\right),\; \operatorname{pauliTwirlWeight}\left(L, b\right) = \operatorname{processMatrix}\left(L, b, b\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.pauliTwirlWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Evaluates the diagonal Pauli process-matrix coefficient q_beta = chi_{beta, beta} of Lambda.

**Definition 1.9 (Aggregated weight-w Pauli-twirl mass).**

$$\forall n \in \mathbb{N},\; \forall L \in \operatorname{QubitMap}\left(n\right),\; \forall w \in \mathbb{N},\; \operatorname{pauliWeightSum}\left(L, w\right) = \sum_{b \in \left\{c \in \operatorname{PauliLabel}\left(n\right) \mid \operatorname{hammingWeight}\left(c\right) = w\right\}} \operatorname{pauliTwirlWeight}\left(L, b\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.pauliWeightSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Sums the diagonal Pauli-twirl weights q_beta(Lambda) over all labels beta of Hamming weight w.

**Definition 1.10 (Normalized maximally entangled state vector).**

$$\forall n \in \mathbb{N},\; \forall p \in \left(\operatorname{QubitIndex}\left(n\right) \times \operatorname{QubitIndex}\left(n\right)\right),\; \operatorname{maxEntangledVec}\left(n\right)\left(p\right) = \operatorname{ite}\left(\operatorname{fst}\left(p\right) = \operatorname{snd}\left(p\right), \operatorname{sqrt}\left(2^{n}\right)^{-1}, 0\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.maxEntangledVec` (`✓ std3`).

*Citation.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Defines the bipartite unit vector |Phi> = 2^{-n/2} sum_x |x> tensor |x> on QubitIndex(n) times QubitIndex(n).

**Definition 1.11 (Maximally entangled rank-one projector).**

$$\forall n \in \mathbb{N},\; \operatorname{maxEntangledProj}\left(n\right) = \operatorname{vecMulVec}\left(\operatorname{maxEntangledVec}\left(n\right), \operatorname{star}\left(\operatorname{maxEntangledVec}\left(n\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.maxEntangledProj` (`✓ std3`).

*Citation.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Forms the rank-one projector |Phi><Phi| = vecMulVec(|Phi>, star |Phi|) of the maximally entangled state.

**Definition 1.12 (Entanglement process fidelity).**

$$\forall n \in \mathbb{N},\; \forall L \in \operatorname{QubitMap}\left(n\right),\; \operatorname{processFidelity}\left(L\right) = \operatorname{dotProduct}\left(\operatorname{star}\left(\operatorname{maxEntangledVec}\left(n\right)\right), \operatorname{mulVec}\left(\operatorname{kron}\left(\operatorname{id}, L\right)\left(\operatorname{maxEntangledProj}\left(n\right)\right), \operatorname{maxEntangledVec}\left(n\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.processFidelity` (`✓ std3`).

*Citation.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Evaluates F(Lambda) = <Phi | (id tensor Lambda)(|Phi><Phi|) | Phi> relative to the identity superoperator.

**Definition 1.13 (Multi-qubit Pauli channel).**

$$\forall n \in \mathbb{N},\; \forall q \in \operatorname{PauliLabel}\left(n\right) \to \mathbb{R},\; \forall X \in \operatorname{Matrix}\left(\operatorname{QubitIndex}\left(n\right), \operatorname{QubitIndex}\left(n\right), \mathbb{C}\right),\; \operatorname{pauliChannel}\left(q\right)\left(X\right) = \sum_{b \in \operatorname{PauliLabel}\left(n\right)} q\left(b\right) \cdot \operatorname{pauliN}\left(n, b\right) \cdot X \cdot \operatorname{pauliN}\left(n, b\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.pauliChannel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Constructs the linear map X |-> sum_beta q_beta P_beta X P_beta associated with real weights q : PauliLabel(n) -> R.

**Definition 1.14 (Complex Pauli-twirled superoperator).**

$$\forall n \in \mathbb{N},\; \forall L \in \operatorname{QubitMap}\left(n\right),\; \forall X \in \operatorname{Matrix}\left(\operatorname{QubitIndex}\left(n\right), \operatorname{QubitIndex}\left(n\right), \mathbb{C}\right),\; \operatorname{complexPauliTwirl}\left(L\right)\left(X\right) = \sum_{b \in \operatorname{PauliLabel}\left(n\right)} \operatorname{pauliTwirlWeight}\left(L, b\right) \cdot \operatorname{pauliN}\left(n, b\right) \cdot X \cdot \operatorname{pauliN}\left(n, b\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.complexPauliTwirl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Constructs the diagonal Pauli map X |-> sum_beta q_beta(Lambda) P_beta X P_beta sharing the Pauli-twirl weights of an arbitrary linear map Lambda.

**Definition 1.15 (Real part of a Pauli-twirl weight).**

$$\forall n \in \mathbb{N},\; \forall L \in \operatorname{QubitMap}\left(n\right),\; \forall b \in \operatorname{PauliLabel}\left(n\right),\; \operatorname{realTwirlWeight}\left(L, b\right) = \operatorname{re}\left(\operatorname{pauliTwirlWeight}\left(L, b\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.realTwirlWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Projects pauliTwirlWeight(Lambda, beta) to its real part.

**Definition 1.16 (Real part of the weight-w Pauli-twirl sum).**

$$\forall n \in \mathbb{N},\; \forall L \in \operatorname{QubitMap}\left(n\right),\; \forall w \in \mathbb{N},\; \operatorname{realWeightSum}\left(L, w\right) = \operatorname{re}\left(\operatorname{pauliWeightSum}\left(L, w\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.realWeightSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Projects pauliWeightSum(Lambda, w) to its real part.

**Definition 1.17 (Real part of entanglement process fidelity).**

$$\forall n \in \mathbb{N},\; \forall L \in \operatorname{QubitMap}\left(n\right),\; \operatorname{realProcessFidelity}\left(L\right) = \operatorname{re}\left(\operatorname{processFidelity}\left(L\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.realProcessFidelity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Projects processFidelity(Lambda) to its real part.

**Definition 1.18 (Single-qubit SIC projector family).**

$$\forall r \in \operatorname{Fin}\left(4\right) \to \operatorname{QubitMatrix},\; \operatorname{IsQubitSICProjector}\left(r\right) \Leftrightarrow \left(\left(\forall a \in \operatorname{Fin}\left(4\right),\; \operatorname{IsHermitian}\left(r\left(a\right)\right) \land \left(r\left(a\right) \cdot r\left(a\right) = r\left(a\right) \land \operatorname{trace}\left(r\left(a\right)\right) = 1\right)\right) \land \left(\forall a \in \operatorname{Fin}\left(4\right),\; \forall b \in \operatorname{Fin}\left(4\right),\; a \ne b \Rightarrow \operatorname{trace}\left(r\left(a\right) \cdot r\left(b\right)\right) = 3^{-1}\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.IsQubitSICProjector` (`✓ std3`).

*Citation.* J. M. Renes, R. Blume-Kohout, A. J. Scott, C. M. Caves (2004). *Symmetric Informationally Complete Quantum Measurements*. DOI: [10.1063/1.1737053](https://doi.org/10.1063/1.1737053). URL: <https://arxiv.org/abs/quant-ph/0310075v1>.

*Commentary.*

Predicates that four 2 by 2 complex matrices are Hermitian, idempotent, unit-trace projectors with pairwise Hilbert-Schmidt inner product 1 / 3.

**Definition 1.19 (Single-qubit unit-vector SIC family).**

$$\forall s \in \operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(2\right) \to \mathbb{C}\right),\; \operatorname{IsUnitVectorQubitSIC}\left(s\right) \Leftrightarrow \left(\left(\forall a \in \operatorname{Fin}\left(4\right),\; \operatorname{dotProduct}\left(\operatorname{star}\left(s\left(a\right)\right), s\left(a\right)\right) = 1\right) \land \left(\forall a \in \operatorname{Fin}\left(4\right),\; \forall b \in \operatorname{Fin}\left(4\right),\; a \ne b \Rightarrow \operatorname{normSq}\left(\operatorname{dotProduct}\left(\operatorname{star}\left(s\left(a\right)\right), s\left(b\right)\right)\right) = 3^{-1}\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.IsUnitVectorQubitSIC` (`✓ std3`).

*Citation.* J. M. Renes, R. Blume-Kohout, A. J. Scott, C. M. Caves (2004). *Symmetric Informationally Complete Quantum Measurements*. DOI: [10.1063/1.1737053](https://doi.org/10.1063/1.1737053). URL: <https://arxiv.org/abs/quant-ph/0310075v1>.

*Commentary.*

Predicates that four vectors in C^2 have unit norm and pairwise squared inner-product modulus 1 / 3.

**Definition 1.20 (Single-qubit SIC overlap matrix B).**

$$\forall a \in \operatorname{Fin}\left(4\right),\; \forall b \in \operatorname{Fin}\left(4\right),\; \operatorname{sicOverlapB}\left(a, b\right) = \operatorname{ite}\left(a = b, 1, 3^{-1}\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.sicOverlapB` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. M. Renes, R. Blume-Kohout, A. J. Scott, C. M. Caves (2004). *Symmetric Informationally Complete Quantum Measurements*. DOI: [10.1063/1.1737053](https://doi.org/10.1063/1.1737053). URL: <https://arxiv.org/abs/quant-ph/0310075v1>.

*Commentary.*

Defines the 4 by 4 overlap matrix B = (2 / 3) I_4 + (1 / 3) J_4 with 1 on the diagonal and 1 / 3 off the diagonal.

**Definition 1.21 (Single-qubit overlap-inverse deviation matrix A).**

$$\forall a \in \operatorname{Fin}\left(4\right),\; \forall b \in \operatorname{Fin}\left(4\right),\; \operatorname{sicMatrixA}\left(a, b\right) = \operatorname{ite}\left(a = b, -4^{-1}, 4^{-1}\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.sicMatrixA` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Defines A = (1 / 4) J_4 - (1 / 2) I_4 with -1 / 4 on the diagonal and 1 / 4 off the diagonal, satisfying B(I_4 - A) = I_4.

**Definition 1.22 (Tensor-product multi-qubit SIC projector).**

$$\forall n \in \mathbb{N},\; \forall r \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(4\right) \to \operatorname{QubitMatrix}\right),\; \forall a \in \operatorname{PauliLabel}\left(n\right),\; \forall x \in \operatorname{QubitIndex}\left(n\right),\; \forall y \in \operatorname{QubitIndex}\left(n\right),\; \operatorname{productSIC}\left(r, a\right)\left(x, y\right) = \prod_{i \in \operatorname{Fin}\left(n\right)} r\left(i\right)\left(a\left(i\right)\right)\left(x\left(i\right), y\left(i\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.productSIC` (`✓ std3`).

*Citation.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Forms the n-qubit tensor-product projector rho^{(1)}_{a_1} tensor ... tensor rho^{(n)}_{a_n} from per-qubit SIC families.

**Definition 1.23 (Subset tensor kernel M_T).**

$$\forall n \in \mathbb{N},\; \forall T \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall a \in \operatorname{PauliLabel}\left(n\right),\; \forall b \in \operatorname{PauliLabel}\left(n\right),\; \operatorname{sicSubsetKernel}\left(n, T, a, b\right) = \prod_{i \in \operatorname{Fin}\left(n\right)} \operatorname{ite}\left(i \in T, \operatorname{sicMatrixA}\left(a\left(i\right), b\left(i\right)\right), \left(\operatorname{I}_{4}\right)\left(a\left(i\right), b\left(i\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.sicSubsetKernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Evaluates the entry (M_T)_{a, b} of the n-fold tensor product placing A on qubit positions in T and I_4 on positions outside T.

**Definition 1.24 (Truncated SIC k-fidelity).**

$$\forall n \in \mathbb{N},\; \forall r \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(4\right) \to \operatorname{QubitMatrix}\right),\; \forall k \in \mathbb{N},\; \forall L \in \operatorname{QubitMap}\left(n\right),\; \operatorname{kFidelity}\left(r, k, L\right) = \left(4^{n}\right)^{-1} \cdot \sum_{T \in \left\{S \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right) \mid \operatorname{card}\left(S\right) \le k\right\}} \left(-1\right)^{\operatorname{card}\left(T\right)} \cdot \left(\sum_{a \in \operatorname{PauliLabel}\left(n\right)} \sum_{b \in \operatorname{PauliLabel}\left(n\right)} \operatorname{sicSubsetKernel}\left(n, T, a, b\right) \cdot \operatorname{trace}\left(\operatorname{productSIC}\left(r, b\right) \cdot L\left(\operatorname{productSIC}\left(r, a\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.kFidelity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Defines F_k(Lambda) = 4^{-n} sum_{|T| <= k} (-1)^{|T|} sum_{a, b} (M_T)_{a, b} Tr(rho_b Lambda(rho_a)) by truncating the overlap-inverse subset expansion to at most k factors of A.

**Definition 1.25 (Real part of the SIC k-fidelity).**

$$\forall n \in \mathbb{N},\; \forall r \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(4\right) \to \operatorname{QubitMatrix}\right),\; \forall k \in \mathbb{N},\; \forall L \in \operatorname{QubitMap}\left(n\right),\; \operatorname{realKFidelity}\left(r, k, L\right) = \operatorname{re}\left(\operatorname{kFidelity}\left(r, k, L\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.realKFidelity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Projects kFidelity(rho, k, Lambda) to its real part.

**Definition 1.26 (Per-qubit diagonal SIC functional e).**

$$\forall r \in \operatorname{Fin}\left(4\right) \to \operatorname{QubitMatrix},\; \forall b \in \operatorname{Fin}\left(4\right),\; \forall g \in \operatorname{Fin}\left(4\right),\; \operatorname{sicE}\left(r, b, g\right) = 4^{-1} \cdot \sum_{a \in \operatorname{Fin}\left(4\right)} \operatorname{trace}\left(r\left(a\right) \cdot \operatorname{pauli1}\left(b\right) \cdot r\left(a\right) \cdot \operatorname{pauli1}\left(g\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.sicE` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. M. Renes, R. Blume-Kohout, A. J. Scott, C. M. Caves (2004). *Symmetric Informationally Complete Quantum Measurements*. DOI: [10.1063/1.1737053](https://doi.org/10.1063/1.1737053). URL: <https://arxiv.org/abs/quant-ph/0310075v1>.

*Commentary.*

Defines e(beta, gamma) = (1 / 4) sum_a Tr(rho_a P_beta rho_a P_gamma) for a single-qubit family rho and Pauli indices beta, gamma.

**Definition 1.27 (Per-qubit A-weighted SIC functional alpha).**

$$\forall r \in \operatorname{Fin}\left(4\right) \to \operatorname{QubitMatrix},\; \forall u \in \operatorname{Fin}\left(4\right),\; \forall v \in \operatorname{Fin}\left(4\right),\; \operatorname{sicAlpha}\left(r, u, v\right) = 4^{-1} \cdot \sum_{a \in \operatorname{Fin}\left(4\right)} \sum_{b \in \operatorname{Fin}\left(4\right)} \operatorname{sicMatrixA}\left(a, b\right) \cdot \operatorname{trace}\left(r\left(b\right) \cdot \operatorname{pauli1}\left(u\right) \cdot r\left(a\right) \cdot \operatorname{pauli1}\left(v\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.sicAlpha` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. M. Renes, R. Blume-Kohout, A. J. Scott, C. M. Caves (2004). *Symmetric Informationally Complete Quantum Measurements*. DOI: [10.1063/1.1737053](https://doi.org/10.1063/1.1737053). URL: <https://arxiv.org/abs/quant-ph/0310075v1>.

*Commentary.*

Defines alpha(beta, gamma) = (1 / 4) sum_{a, b} A_{a, b} Tr(rho_b P_beta rho_a P_gamma) for a single-qubit family rho and Pauli indices beta, gamma.

**Theorem 1.28 (Pauli process-matrix expansion, process fidelity identity, and CP/TP properties).**

$$\forall n \in \mathbb{N},\; \left(\forall L \in \operatorname{QubitMap}\left(n\right),\; \left(\forall X \in \operatorname{Matrix}\left(\operatorname{QubitIndex}\left(n\right), \operatorname{QubitIndex}\left(n\right), \mathbb{C}\right),\; L\left(X\right) = \sum_{b \in \operatorname{PauliLabel}\left(n\right)} \sum_{g \in \operatorname{PauliLabel}\left(n\right)} \operatorname{processMatrix}\left(L, b, g\right) \cdot \operatorname{pauliN}\left(n, b\right) \cdot X \cdot \operatorname{pauliN}\left(n, g\right)\right) \land \left(\forall c \in \operatorname{PauliLabel}\left(n\right) \to \left(\operatorname{PauliLabel}\left(n\right) \to \mathbb{C}\right),\; \left(\forall X \in \operatorname{Matrix}\left(\operatorname{QubitIndex}\left(n\right), \operatorname{QubitIndex}\left(n\right), \mathbb{C}\right),\; L\left(X\right) = \sum_{b \in \operatorname{PauliLabel}\left(n\right)} \sum_{g \in \operatorname{PauliLabel}\left(n\right)} c\left(b, g\right) \cdot \operatorname{pauliN}\left(n, b\right) \cdot X \cdot \operatorname{pauliN}\left(n, g\right)\right) \Rightarrow \left(\forall b \in \operatorname{PauliLabel}\left(n\right),\; \forall g \in \operatorname{PauliLabel}\left(n\right),\; c\left(b, g\right) = \operatorname{processMatrix}\left(L, b, g\right)\right)\right)\right) \land \left(\left(\forall L \in \operatorname{QubitMap}\left(n\right),\; \operatorname{processFidelity}\left(L\right) = \operatorname{pauliTwirlWeight}\left(L, 0\right) \land \left(\operatorname{pauliWeightSum}\left(L, 0\right) = \operatorname{pauliTwirlWeight}\left(L, 0\right) \land \sum_{w \in \operatorname{range}\left(n + 1\right)} \operatorname{pauliWeightSum}\left(L, w\right) = \sum_{b \in \operatorname{PauliLabel}\left(n\right)} \operatorname{pauliTwirlWeight}\left(L, b\right)\right)\right) \land \left(\left(\forall L \in \operatorname{QubitMap}\left(n\right),\; \left(\operatorname{IsTracePreserving}\left(L\right) \Leftrightarrow \sum_{b \in \operatorname{PauliLabel}\left(n\right)} \sum_{g \in \operatorname{PauliLabel}\left(n\right)} \operatorname{processMatrix}\left(L, b, g\right) \cdot \operatorname{pauliN}\left(n, g\right) \cdot \operatorname{pauliN}\left(n, b\right) = 1\right) \land \left(\operatorname{IsTracePreserving}\left(L\right) \Rightarrow \left(\sum_{b \in \operatorname{PauliLabel}\left(n\right)} \operatorname{pauliTwirlWeight}\left(L, b\right) = 1 \land \sum_{w \in \operatorname{range}\left(n + 1\right)} \operatorname{pauliWeightSum}\left(L, w\right) = 1\right)\right)\right) \land \left(\left(\forall L \in \operatorname{QubitMap}\left(n\right),\; \operatorname{IsCompletelyPositive}\left(L\right) \Rightarrow \left(\left(\forall b \in \operatorname{PauliLabel}\left(n\right),\; \operatorname{im}\left(\operatorname{pauliTwirlWeight}\left(L, b\right)\right) = 0 \land 0 \le \operatorname{re}\left(\operatorname{pauliTwirlWeight}\left(L, b\right)\right)\right) \land \left(\left(\forall w \in \mathbb{N},\; \operatorname{ofReal}\left(\operatorname{realWeightSum}\left(L, w\right)\right) = \operatorname{pauliWeightSum}\left(L, w\right) \land 0 \le \operatorname{realWeightSum}\left(L, w\right)\right) \land \operatorname{ofReal}\left(\operatorname{realProcessFidelity}\left(L\right)\right) = \operatorname{processFidelity}\left(L\right)\right)\right)\right) \land \left(\forall q \in \operatorname{PauliLabel}\left(n\right) \to \mathbb{R},\; \left(\forall b \in \operatorname{PauliLabel}\left(n\right),\; \forall g \in \operatorname{PauliLabel}\left(n\right),\; \operatorname{processMatrix}\left(\operatorname{pauliChannel}\left(q\right), b, g\right) = \operatorname{ite}\left(b = g, \operatorname{ofReal}\left(q\left(b\right)\right), 0\right)\right) \land \left(\left(\left(\forall b \in \operatorname{PauliLabel}\left(n\right),\; 0 \le q\left(b\right)\right) \Rightarrow \operatorname{IsCompletelyPositive}\left(\operatorname{pauliChannel}\left(q\right)\right)\right) \land \left(\sum_{b \in \operatorname{PauliLabel}\left(n\right)} q\left(b\right) = 1 \Rightarrow \operatorname{IsTracePreserving}\left(\operatorname{pauliChannel}\left(q\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.pauli_process_matrix_and_fidelity_characterization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Every n-qubit linear map Lambda admits a unique expansion Lambda(X) = sum_{beta, gamma} chi_{beta, gamma} P_beta X P_gamma with chi = processMatrix(Lambda), satisfies F(Lambda) = q_0(Lambda) = Q_0(Lambda) and sum_{w=0}^n Q_w(Lambda) = sum_beta q_beta(Lambda), is trace-preserving if and only if sum_{beta, gamma} chi_{beta, gamma} P_gamma P_beta = I (which implies sum_beta q_beta(Lambda) = sum_{w=0}^n Q_w(Lambda) = 1), has real nonnegative Pauli-twirl weights whenever Lambda is completely positive, and conversely every nonnegative weight vector q defines a completely positive Pauli channel that is trace-preserving when sum_beta q_beta = 1.

**Theorem 1.29 (Equivalence of projector and unit-vector single-qubit SICs).**

$$\forall r \in \operatorname{Fin}\left(4\right) \to \operatorname{QubitMatrix},\; \operatorname{IsQubitSICProjector}\left(r\right) \Leftrightarrow \left(\exists s \in \operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(2\right) \to \mathbb{C}\right),\; \operatorname{IsUnitVectorQubitSIC}\left(s\right) \land \left(\forall a \in \operatorname{Fin}\left(4\right),\; r\left(a\right) = \operatorname{rankOneDensity}\left(s\left(a\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.isQubitSICProjector_iff_exists_unitVectorQubitSIC` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. M. Renes, R. Blume-Kohout, A. J. Scott, C. M. Caves (2004). *Symmetric Informationally Complete Quantum Measurements*. DOI: [10.1063/1.1737053](https://doi.org/10.1063/1.1737053). URL: <https://arxiv.org/abs/quant-ph/0310075v1>.

*Commentary.*

A family of four 2 by 2 complex matrices satisfies IsQubitSICProjector if and only if its members are the rank-one density matrices of four unit vectors in C^2 satisfying IsUnitVectorQubitSIC.

**Theorem 1.30 (Overlap-inverse matrices, 2-design moments, diagonal per-qubit functionals, and SIC-choice independence).**

$$\forall n \in \mathbb{N},\; \left(\operatorname{sicOverlapB} \cdot \left(1 - \operatorname{sicMatrixA}\right) = 1 \land \left(1 - \operatorname{sicMatrixA}\right) \cdot \operatorname{sicOverlapB} = 1\right) \land \left(\left(\forall a \in \operatorname{Fin}\left(4\right),\; \left(\operatorname{sicOverlapB} \cdot \left(1 - \operatorname{matrixOf}\left(\left(\lambda i \in \operatorname{Fin}\left(4\right), j \in \operatorname{Fin}\left(4\right) \mapsto \frac{1 - \operatorname{ite}\left(i = j, 5, 0\right)}{4}\right)\right)\right)\right)\left(a, a\right) = \frac{7}{4}\right) \land \left(\left(\forall a \in \operatorname{PauliLabel}\left(n\right),\; \forall b \in \operatorname{PauliLabel}\left(n\right),\; \prod_{i \in \operatorname{Fin}\left(n\right)} \left(1 - \operatorname{sicMatrixA}\right)\left(a\left(i\right), b\left(i\right)\right) = \sum_{T \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)} \left(-1\right)^{\operatorname{card}\left(T\right)} \cdot \operatorname{sicSubsetKernel}\left(n, T, a, b\right) \land \prod_{i \in \operatorname{Fin}\left(n\right)} \left(1 - \operatorname{sicMatrixA}\right)\left(a\left(i\right), b\left(i\right)\right) = \frac{\left(-1\right)^{\operatorname{card}\left(\left\{i \in \operatorname{Fin}\left(n\right) \mid a\left(i\right) \ne b\left(i\right)\right\}\right)} \cdot 5^{n - \operatorname{card}\left(\left\{i \in \operatorname{Fin}\left(n\right) \mid a\left(i\right) \ne b\left(i\right)\right\}\right)}}{4^{n}}\right) \land \left(\left(\forall r \in \operatorname{Fin}\left(4\right) \to \operatorname{QubitMatrix},\; \operatorname{IsQubitSICProjector}\left(r\right) \Rightarrow \left(\left(\forall u \in \operatorname{Fin}\left(2\right),\; \forall v \in \operatorname{Fin}\left(2\right),\; \forall x \in \operatorname{Fin}\left(2\right),\; \forall y \in \operatorname{Fin}\left(2\right),\; \sum_{a \in \operatorname{Fin}\left(4\right)} r\left(a\right)\left(u, x\right) \cdot r\left(a\right)\left(v, y\right) = \frac{2}{3} \cdot \left(\operatorname{ite}\left(u = x \land v = y, 1, 0\right) + \operatorname{ite}\left(u = y \land v = x, 1, 0\right)\right)\right) \land \left(\sum_{a \in \operatorname{Fin}\left(4\right)} r\left(a\right) = 2 \cdot \operatorname{I}_{2} \land \left(\left(\forall X \in \operatorname{QubitMatrix},\; \forall Y \in \operatorname{QubitMatrix},\; \sum_{a \in \operatorname{Fin}\left(4\right)} \operatorname{trace}\left(r\left(a\right) \cdot X\right) \cdot \operatorname{trace}\left(r\left(a\right) \cdot Y\right) = \frac{2}{3} \cdot \left(\operatorname{trace}\left(X \cdot Y\right) + \operatorname{trace}\left(X\right) \cdot \operatorname{trace}\left(Y\right)\right)\right) \land \left(\left(\forall b \in \operatorname{Fin}\left(4\right),\; \forall g \in \operatorname{Fin}\left(4\right),\; \operatorname{sicE}\left(r, b, g\right) = \operatorname{ite}\left(b = g, \operatorname{ite}\left(b = 0, 1, 3^{-1}\right), 0\right)\right) \land \left(\forall b \in \operatorname{Fin}\left(4\right),\; \forall g \in \operatorname{Fin}\left(4\right),\; \operatorname{sicAlpha}\left(r, b, g\right) = \operatorname{ite}\left(b = g, \operatorname{ite}\left(b = 0, 0, 3^{-1}\right), 0\right)\right)\right)\right)\right)\right)\right) \land \left(\left(\forall r \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(4\right) \to \operatorname{QubitMatrix}\right),\; \forall T \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall b \in \operatorname{PauliLabel}\left(n\right),\; \forall g \in \operatorname{PauliLabel}\left(n\right),\; \left(4^{n}\right)^{-1} \cdot \sum_{a \in \operatorname{PauliLabel}\left(n\right)} \sum_{c \in \operatorname{PauliLabel}\left(n\right)} \operatorname{sicSubsetKernel}\left(n, T, a, c\right) \cdot \operatorname{trace}\left(\operatorname{productSIC}\left(r, c\right) \cdot \operatorname{pauliN}\left(n, b\right) \cdot \operatorname{productSIC}\left(r, a\right) \cdot \operatorname{pauliN}\left(n, g\right)\right) = \prod_{i \in \operatorname{Fin}\left(n\right)} \operatorname{ite}\left(i \in T, \operatorname{sicAlpha}\left(r\left(i\right), b\left(i\right), g\left(i\right)\right), \operatorname{sicE}\left(r\left(i\right), b\left(i\right), g\left(i\right)\right)\right)\right) \land \left(\left(\forall r \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(4\right) \to \operatorname{QubitMatrix}\right),\; \left(\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{IsQubitSICProjector}\left(r\left(i\right)\right)\right) \Rightarrow \left(\forall k \in \mathbb{N},\; \forall L \in \operatorname{QubitMap}\left(n\right),\; \operatorname{kFidelity}\left(r, k, L\right) = \sum_{b \in \operatorname{PauliLabel}\left(n\right)} \operatorname{pauliTwirlWeight}\left(L, b\right) \cdot \left(\sum_{T \in \left\{S \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right) \mid \operatorname{card}\left(S\right) \le k\right\}} \left(-1\right)^{\operatorname{card}\left(T\right)} \cdot \left(\prod_{i \in T} \operatorname{sicAlpha}\left(r\left(i\right), b\left(i\right), b\left(i\right)\right)\right) \cdot \left(\prod_{i \in T^{c}} \operatorname{sicE}\left(r\left(i\right), b\left(i\right), b\left(i\right)\right)\right)\right) \land \operatorname{kFidelity}\left(r, k, L\right) = \operatorname{kFidelity}\left(r, k, \operatorname{complexPauliTwirl}\left(L\right)\right)\right)\right) \land \left(\forall r \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(4\right) \to \operatorname{QubitMatrix}\right),\; \forall s \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(4\right) \to \operatorname{QubitMatrix}\right),\; \left(\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{IsQubitSICProjector}\left(r\left(i\right)\right)\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{IsQubitSICProjector}\left(s\left(i\right)\right)\right) \Rightarrow \left(\forall k \in \mathbb{N},\; \forall L \in \operatorname{QubitMap}\left(n\right),\; \operatorname{kFidelity}\left(r, k, L\right) = \operatorname{kFidelity}\left(s, k, L\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.qubit_sic_matrices_and_per_qubit_traces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. M. Renes, R. Blume-Kohout, A. J. Scott, C. M. Caves (2004). *Symmetric Informationally Complete Quantum Measurements*. DOI: [10.1063/1.1737053](https://doi.org/10.1063/1.1737053). URL: <https://arxiv.org/abs/quant-ph/0310075v1>.

*Commentary.*

Establishes B(I_4 - A) = (I_4 - A)B = I_4 whereas the matrix with entries (1 - 5 delta_{i,j}) / 4 gives diagonal entries 7 / 4 in B(I_4 - A'); proves the n-qubit inverse expansion prod_i (I_4 - A)_{a_i, b_i} = sum_T (-1)^{|T|} (M_T)_{a, b} = (-1)^m 5^{n - m} / 4^n where m is the number of qubits with a_i != b_i; derives the single-qubit 2-design identities, sum_a rho_a = 2 I_2, e(0, 0) = 1, alpha(0, 0) = 0, and e(beta, beta) = alpha(beta, beta) = 1 / 3 for nonzero beta with off-diagonal vanishing; factors the n-qubit subset trace across T and its complement; and deduces that F_k(Lambda) depends only on the Pauli-twirl weights q_beta(Lambda), agrees with F_k of the Pauli-twirled map, and is independent of the chosen single-qubit SICs.

**Theorem 1.31 (Universal Pauli-weight alternating binomial formula for SIC k-fidelities).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall r \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(4\right) \to \operatorname{QubitMatrix}\right),\; \left(\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{IsQubitSICProjector}\left(r\left(i\right)\right)\right) \Rightarrow \left(\forall L \in \operatorname{QubitMap}\left(n\right),\; \operatorname{kFidelity}\left(r, k, L\right) = \operatorname{pauliWeightSum}\left(L, 0\right) + \left(-1\right)^{k} \cdot \sum_{w \in \operatorname{Icc}\left(1, n\right)} \left(3^{-1}\right)^{w} \cdot \operatorname{choose}\left(w - 1, k\right) \cdot \operatorname{pauliWeightSum}\left(L, w\right) \land \left(\left(n \le k \Rightarrow \operatorname{kFidelity}\left(r, k, L\right) = \operatorname{processFidelity}\left(L\right)\right) \land \left(\operatorname{kFidelity}\left(r, 0, L\right) = \sum_{b \in \operatorname{PauliLabel}\left(n\right)} \left(3^{-1}\right)^{\operatorname{hammingWeight}\left(b\right)} \cdot \operatorname{pauliTwirlWeight}\left(L, b\right) \land \left(\operatorname{IsCompletelyPositive}\left(L\right) \Rightarrow \left(\operatorname{ofReal}\left(\operatorname{realKFidelity}\left(r, k, L\right)\right) = \operatorname{kFidelity}\left(r, k, L\right) \land \operatorname{realKFidelity}\left(r, k, L\right) = \operatorname{realWeightSum}\left(L, 0\right) + \left(-1\right)^{k} \cdot \sum_{w \in \operatorname{Icc}\left(1, n\right)} \left(3^{-1}\right)^{w} \cdot \operatorname{choose}\left(w - 1, k\right) \cdot \operatorname{realWeightSum}\left(L, w\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.kFidelity_eq_pauliWeight_alternating_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

For every n, k, every choice of single-qubit SICs, and every complex-linear map Lambda on M_{2^n}(C), F_k(Lambda) = Q_0(Lambda) + (-1)^k sum_{w=1}^n 3^{-w} C(w - 1, k) Q_w(Lambda). Consequently F_k(Lambda) = F(Lambda) for all k >= n, F_0(Lambda) = sum_beta 3^{-|beta|} q_beta(Lambda), and for completely positive Lambda the complex k-fidelity equals its real projection with real weight sums.

**Theorem 1.32 (Alternating truncation error identity and support characterization for completely positive maps).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall r \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(4\right) \to \operatorname{QubitMatrix}\right),\; \left(\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{IsQubitSICProjector}\left(r\left(i\right)\right)\right) \Rightarrow \left(\forall L \in \operatorname{QubitMap}\left(n\right),\; \operatorname{IsCompletelyPositive}\left(L\right) \Rightarrow \left(\left(-1\right)^{k} \cdot \left(\operatorname{realKFidelity}\left(r, k, L\right) - \operatorname{realProcessFidelity}\left(L\right)\right) = \sum_{w \in \operatorname{Icc}\left(k + 1, n\right)} \left(3^{-1}\right)^{w} \cdot \operatorname{choose}\left(w - 1, k\right) \cdot \operatorname{realWeightSum}\left(L, w\right) \land \left(0 \le \sum_{w \in \operatorname{Icc}\left(k + 1, n\right)} \left(3^{-1}\right)^{w} \cdot \operatorname{choose}\left(w - 1, k\right) \cdot \operatorname{realWeightSum}\left(L, w\right) \land \left(\left(\operatorname{Odd}\left(k\right) \Rightarrow \operatorname{realKFidelity}\left(r, k, L\right) \le \operatorname{realProcessFidelity}\left(L\right)\right) \land \left(\left(\operatorname{Even}\left(k\right) \Rightarrow \operatorname{realProcessFidelity}\left(L\right) \le \operatorname{realKFidelity}\left(r, k, L\right)\right) \land \left(\left(\forall i \in \mathbb{N},\; \forall j \in \mathbb{N},\; \operatorname{Odd}\left(j\right) \Rightarrow \left(\operatorname{Even}\left(i\right) \Rightarrow \operatorname{realKFidelity}\left(r, j, L\right) \le \operatorname{realKFidelity}\left(r, i, L\right)\right)\right) \land \left(\left(\operatorname{realKFidelity}\left(r, k, L\right) = \operatorname{realProcessFidelity}\left(L\right) \Leftrightarrow \left(\forall w \in \operatorname{Icc}\left(k + 1, n\right),\; \operatorname{realWeightSum}\left(L, w\right) = 0\right)\right) \land \left(\operatorname{realKFidelity}\left(r, k, L\right) = \operatorname{realProcessFidelity}\left(L\right) \Leftrightarrow \left(\forall b \in \operatorname{PauliLabel}\left(n\right),\; k < \operatorname{hammingWeight}\left(b\right) \Rightarrow \operatorname{realTwirlWeight}\left(L, b\right) = 0\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.cp_kFidelity_alternating_truncation_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

For every completely positive n-qubit map Lambda and every k, (-1)^k (F_k(Lambda) - F(Lambda)) = sum_{w=k+1}^n 3^{-w} C(w - 1, k) Q_w(Lambda) >= 0, yielding F_k(Lambda) <= F(Lambda) for odd k, F(Lambda) <= F_k(Lambda) for even k, F_j(Lambda) <= F_i(Lambda) for all odd j and even i, and equality F_k(Lambda) = F(Lambda) if and only if Q_w(Lambda) = 0 for all w >= k + 1, equivalently q_beta(Lambda) = 0 whenever |beta| > k.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.IsQubitSICProjector`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.IsUnitVectorQubitSIC`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.PauliLabel`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.QubitIndex`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.QubitMap`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.complexPauliTwirl`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.cp_kFidelity_alternating_truncation_bound`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.hammingWeight`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.isQubitSICProjector_iff_exists_unitVectorQubitSIC`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.kFidelity`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.kFidelity_eq_pauliWeight_alternating_sum`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.maxEntangledProj`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.maxEntangledVec`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.pauli1`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.pauliChannel`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.pauliN`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.pauliTwirlWeight`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.pauliWeightSum`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.pauli_process_matrix_and_fidelity_characterization`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.processFidelity`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.processMatrix`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.productSIC`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.qubit_sic_matrices_and_per_qubit_traces`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.realKFidelity`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.realProcessFidelity`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.realTwirlWeight`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.realWeightSum`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.sicAlpha`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.sicE`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.sicMatrixA`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.sicOverlapB`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.sicSubsetKernel`
- Dependency: [D5/S3/Quantum/FiniteDimensional](../../FiniteDimensional.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../../Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../../Foundation/FiniteKrausRepresentation.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../../PureState/PureStateHandshake.md)
