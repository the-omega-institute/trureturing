# Pauli-weight expansion and alternating truncation bounds for qubit SIC k-fidelities

## Abstract

Multi-qubit Pauli process matrices, Pauli-twirl weight distributions, single-qubit SIC projectors and overlap-inverse kernels, per-qubit diagonal functionals, the alternating binomial Pauli-weight formula for every SIC k-fidelity of an arbitrary linear qubit map, and alternating truncation bounds for completely positive maps.

**Definition 1.1 (Computational basis index).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.QubitIndex`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.QubitIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

For n qubits, QubitIndex(n) is the function type Fin n -> Fin 2 indexing the 2^n computational basis vectors.

**Definition 1.2 (Multi-qubit Pauli string label).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.PauliLabel`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.PauliLabel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

For n qubits, PauliLabel(n) is the function type Fin n -> Fin 4 indexing the 4^n tensor-product Pauli strings.

**Definition 1.3 (Linear superoperator on n qubits).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.QubitMap`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.QubitMap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

For n qubits, QubitMap(n) is the space of complex-linear maps on 2^n by 2^n complex matrices.

**Definition 1.4 (Single-qubit Pauli matrices).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.pauli1`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.pauli1` (`✓ std3`).

*Citation.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Maps 0, 1, 2, 3 in Fin 4 to the 2 by 2 complex matrices I, X, Y, Z.

**Definition 1.5 (Tensor-product Pauli operator).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.pauliN`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.pauliN` (`✓ std3`).

*Citation.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

For a multi-qubit label beta in PauliLabel(n), pauliN(n, beta) is the n-fold tensor-product matrix whose (x, y) entry is the product over i in Fin n of pauli1(beta(i))(x(i), y(i)).

**Definition 1.6 (Pauli Hamming weight).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.hammingWeight`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.hammingWeight` (`✓ std3`).

*Citation.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Counts the number of qubit positions i in Fin n at which beta(i) is nonzero.

**Definition 1.7 (Pauli process-matrix coefficients).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.processMatrix`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.processMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Gives the unique expansion coefficient chi_{beta, gamma} of an n-qubit linear map Lambda in the basis X |-> P_beta X P_gamma by Hilbert-Schmidt contraction scaled by 4^{-n}.

**Definition 1.8 (Diagonal Pauli-twirl weight).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.pauliTwirlWeight`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.pauliTwirlWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Evaluates the diagonal Pauli process-matrix coefficient q_beta = chi_{beta, beta} of Lambda.

**Definition 1.9 (Aggregated weight-w Pauli-twirl mass).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.pauliWeightSum`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.pauliWeightSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Sums the diagonal Pauli-twirl weights q_beta(Lambda) over all labels beta of Hamming weight w.

**Definition 1.10 (Normalized maximally entangled state vector).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.maxEntangledVec`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.maxEntangledVec` (`✓ std3`).

*Citation.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Defines the bipartite unit vector |Phi> = 2^{-n/2} sum_x |x> tensor |x> on QubitIndex(n) times QubitIndex(n).

**Definition 1.11 (Maximally entangled rank-one projector).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.maxEntangledProj`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.maxEntangledProj` (`✓ std3`).

*Citation.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Forms the rank-one projector |Phi><Phi| = vecMulVec(|Phi>, star |Phi|) of the maximally entangled state.

**Definition 1.12 (Entanglement process fidelity).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.processFidelity`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.processFidelity` (`✓ std3`).

*Citation.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Evaluates F(Lambda) = <Phi | (id tensor Lambda)(|Phi><Phi|) | Phi> relative to the identity superoperator.

**Definition 1.13 (Multi-qubit Pauli channel).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.pauliChannel`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.pauliChannel` (`✓ std3`).

*Citation.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Constructs the linear map X |-> sum_beta q_beta P_beta X P_beta associated with real weights q : PauliLabel(n) -> R.

**Definition 1.14 (Complex Pauli-twirled superoperator).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.complexPauliTwirl`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.complexPauliTwirl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Constructs the diagonal Pauli map X |-> sum_beta q_beta(Lambda) P_beta X P_beta sharing the Pauli-twirl weights of an arbitrary linear map Lambda.

**Definition 1.15 (Real part of a Pauli-twirl weight).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.realTwirlWeight`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.realTwirlWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Projects pauliTwirlWeight(Lambda, beta) to its real part.

**Definition 1.16 (Real part of the weight-w Pauli-twirl sum).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.realWeightSum`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.realWeightSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Projects pauliWeightSum(Lambda, w) to its real part.

**Definition 1.17 (Real part of entanglement process fidelity).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.realProcessFidelity`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.realProcessFidelity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Projects processFidelity(Lambda) to its real part.

**Definition 1.18 (Single-qubit SIC projector family).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.IsQubitSICProjector`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.IsQubitSICProjector` (`✓ std3`).

*Citation.* J. M. Renes, R. Blume-Kohout, A. J. Scott, C. M. Caves (2004). *Symmetric Informationally Complete Quantum Measurements*. DOI: [10.1063/1.1737053](https://doi.org/10.1063/1.1737053). URL: <https://arxiv.org/abs/quant-ph/0310075v1>.

*Commentary.*

Predicates that four 2 by 2 complex matrices are Hermitian, idempotent, unit-trace projectors with pairwise Hilbert-Schmidt inner product 1 / 3.

**Definition 1.19 (Single-qubit unit-vector SIC family).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.IsUnitVectorQubitSIC`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.IsUnitVectorQubitSIC` (`✓ std3`).

*Citation.* J. M. Renes, R. Blume-Kohout, A. J. Scott, C. M. Caves (2004). *Symmetric Informationally Complete Quantum Measurements*. DOI: [10.1063/1.1737053](https://doi.org/10.1063/1.1737053). URL: <https://arxiv.org/abs/quant-ph/0310075v1>.

*Commentary.*

Predicates that four vectors in C^2 have unit norm and pairwise squared inner-product modulus 1 / 3.

**Definition 1.20 (Single-qubit SIC overlap matrix B).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.sicOverlapB`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.sicOverlapB` (`✓ std3`).

*Citation.* J. M. Renes, R. Blume-Kohout, A. J. Scott, C. M. Caves (2004). *Symmetric Informationally Complete Quantum Measurements*. DOI: [10.1063/1.1737053](https://doi.org/10.1063/1.1737053). URL: <https://arxiv.org/abs/quant-ph/0310075v1>.

*Commentary.*

Defines the 4 by 4 overlap matrix B = (2 / 3) I_4 + (1 / 3) J_4 with 1 on the diagonal and 1 / 3 off the diagonal.

**Definition 1.21 (Single-qubit overlap-inverse deviation matrix A).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.sicMatrixA`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.sicMatrixA` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Defines A = (1 / 4) J_4 - (1 / 2) I_4 with -1 / 4 on the diagonal and 1 / 4 off the diagonal, satisfying B(I_4 - A) = I_4.

**Definition 1.22 (Tensor-product multi-qubit SIC projector).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.productSIC`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.productSIC` (`✓ std3`).

*Citation.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Forms the n-qubit tensor-product projector rho^{(1)}_{a_1} tensor ... tensor rho^{(n)}_{a_n} from per-qubit SIC families.

**Definition 1.23 (Subset tensor kernel M_T).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.sicSubsetKernel`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.sicSubsetKernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Evaluates the entry (M_T)_{a, b} of the n-fold tensor product placing A on qubit positions in T and I_4 on positions outside T.

**Definition 1.24 (Truncated SIC k-fidelity).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.kFidelity`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.kFidelity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Defines F_k(Lambda) = 4^{-n} sum_{|T| <= k} (-1)^{|T|} sum_{a, b} (M_T)_{a, b} Tr(rho_b Lambda(rho_a)) by truncating the overlap-inverse subset expansion to at most k factors of A.

**Definition 1.25 (Real part of the SIC k-fidelity).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.realKFidelity`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.realKFidelity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Projects kFidelity(rho, k, Lambda) to its real part.

**Definition 1.26 (Per-qubit diagonal SIC functional e).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.sicE`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.sicE` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. M. Renes, R. Blume-Kohout, A. J. Scott, C. M. Caves (2004). *Symmetric Informationally Complete Quantum Measurements*. DOI: [10.1063/1.1737053](https://doi.org/10.1063/1.1737053). URL: <https://arxiv.org/abs/quant-ph/0310075v1>.

*Commentary.*

Defines e(beta, gamma) = (1 / 4) sum_a Tr(rho_a P_beta rho_a P_gamma) for a single-qubit family rho and Pauli indices beta, gamma.

**Definition 1.27 (Per-qubit A-weighted SIC functional alpha).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.sicAlpha`

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.sicAlpha` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. M. Renes, R. Blume-Kohout, A. J. Scott, C. M. Caves (2004). *Symmetric Informationally Complete Quantum Measurements*. DOI: [10.1063/1.1737053](https://doi.org/10.1063/1.1737053). URL: <https://arxiv.org/abs/quant-ph/0310075v1>.

*Commentary.*

Defines alpha(beta, gamma) = (1 / 4) sum_{a, b} A_{a, b} Tr(rho_b P_beta rho_a P_gamma) for a single-qubit family rho and Pauli indices beta, gamma.

**Theorem 1.28 (Pauli process-matrix expansion, process fidelity identity, and CP/TP properties).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.pauli_process_matrix_and_fidelity_characterization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.pauli_process_matrix_and_fidelity_characterization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Every n-qubit linear map Lambda admits a unique expansion Lambda(X) = sum_{beta, gamma} chi_{beta, gamma} P_beta X P_gamma with chi = processMatrix(Lambda), satisfies F(Lambda) = q_0(Lambda) = Q_0(Lambda) and sum_{w=0}^n Q_w(Lambda) = sum_beta q_beta(Lambda), is trace-preserving if and only if sum_{beta, gamma} chi_{beta, gamma} P_gamma P_beta = I (which implies sum_beta q_beta(Lambda) = sum_{w=0}^n Q_w(Lambda) = 1), has real nonnegative Pauli-twirl weights whenever Lambda is completely positive, and conversely every nonnegative weight vector q defines a completely positive Pauli channel that is trace-preserving when sum_beta q_beta = 1.

**Theorem 1.29 (Equivalence of projector and unit-vector single-qubit SICs).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.isQubitSICProjector_iff_exists_unitVectorQubitSIC`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.isQubitSICProjector_iff_exists_unitVectorQubitSIC` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. M. Renes, R. Blume-Kohout, A. J. Scott, C. M. Caves (2004). *Symmetric Informationally Complete Quantum Measurements*. DOI: [10.1063/1.1737053](https://doi.org/10.1063/1.1737053). URL: <https://arxiv.org/abs/quant-ph/0310075v1>.

*Commentary.*

A family of four 2 by 2 complex matrices satisfies IsQubitSICProjector if and only if its members are the rank-one density matrices of four unit vectors in C^2 satisfying IsUnitVectorQubitSIC.

**Theorem 1.30 (Overlap-inverse matrices, 2-design moments, diagonal per-qubit functionals, and SIC-choice independence).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.qubit_sic_matrices_and_per_qubit_traces`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.qubit_sic_matrices_and_per_qubit_traces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. M. Renes, R. Blume-Kohout, A. J. Scott, C. M. Caves (2004). *Symmetric Informationally Complete Quantum Measurements*. DOI: [10.1063/1.1737053](https://doi.org/10.1063/1.1737053). URL: <https://arxiv.org/abs/quant-ph/0310075v1>.

*Commentary.*

Establishes B(I_4 - A) = (I_4 - A)B = I_4 whereas the matrix with entries (1 - 5 delta_{i,j}) / 4 gives diagonal entries 7 / 4 in B(I_4 - A'); proves the n-qubit inverse expansion prod_i (I_4 - A)_{a_i, b_i} = sum_T (-1)^{|T|} (M_T)_{a, b} = (-1)^m 5^{n - m} / 4^n where m is the number of qubits with a_i != b_i; derives the single-qubit 2-design identities, sum_a rho_a = 2 I_2, e(0, 0) = 1, alpha(0, 0) = 0, and e(beta, beta) = alpha(beta, beta) = 1 / 3 for nonzero beta with off-diagonal vanishing; factors the n-qubit subset trace across T and its complement; and deduces that F_k(Lambda) depends only on the Pauli-twirl weights q_beta(Lambda), agrees with F_k of the Pauli-twirled map, and is independent of the chosen single-qubit SICs.

**Theorem 1.31 (Universal Pauli-weight alternating binomial formula for SIC k-fidelities).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.kFidelity_eq_pauliWeight_alternating_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.kFidelity_eq_pauliWeight_alternating_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

For every n, k, every choice of single-qubit SICs, and every complex-linear map Lambda on M_{2^n}(C), F_k(Lambda) = Q_0(Lambda) + (-1)^k sum_{w=1}^n 3^{-w} C(w - 1, k) Q_w(Lambda). Consequently F_k(Lambda) = F(Lambda) for all k >= n, F_0(Lambda) = sum_beta 3^{-|beta|} q_beta(Lambda), and for completely positive Lambda the complex k-fidelity equals its real projection with real weight sums.

**Theorem 1.32 (Alternating truncation error identity and support characterization for completely positive maps).**

Lean statement: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.cp_kFidelity_alternating_truncation_bound`

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
