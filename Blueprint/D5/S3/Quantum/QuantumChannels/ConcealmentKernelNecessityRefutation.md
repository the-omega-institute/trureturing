# Concealment does not determine the adjoint kernel

## Abstract

Complete dephasing and complete depolarization on a qubit conceal every pair of finite POVMs, although their adjoint kernels on Hermitian operators are different.

**Definition 1.1 (Finite POVMs).**

$$\forall d \in \mathbb{N},\; \forall Omega \in Type,\; [\operatorname{Fintype}\left(Omega\right)] \forall M \in Omega \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{IsPOVM}\left(M\right) \Leftrightarrow ((\forall a \in Omega,\; \operatorname{PosSemidef}\left(M\left(a\right)\right)) \land (\sum_{a : Omega} (M\left(a\right)) = 1))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM` (`✓ std3`).

*Citation.* Mohd Asad Siddiqui; Zizhu Wang (2026). *Operational Concealment of Measurement Incompatibility by Quantum Channels: Rank Loss versus Contraction*. DOI: [10.48550/arXiv.2607.11762](https://doi.org/10.48550/arXiv.2607.11762). URL: <https://arxiv.org/abs/2607.11762v2>.

*Commentary.*

For a finite outcome type Omega, a POVM consists of positive semidefinite complex d by d matrices whose sum is the identity. Zero effects are allowed. Positivity includes Hermitian symmetry.

**Lemma 1.2 (Nonnegative normalized diagonal entries define a POVM).**

$$\forall d \in \mathbb{N},\; \forall Omega \in Type,\; [\operatorname{Fintype}\left(Omega\right)] \forall p \in Omega \to \left(\operatorname{Fin}\left(d\right) \to \mathbb{R}\right),\; ((\forall a \in Omega,\; \forall i \in \operatorname{Fin}\left(d\right),\; 0 \le p\left(a, i\right)) \land (\forall i \in \operatorname{Fin}\left(d\right),\; \sum_{a : Omega} (p\left(a, i\right)) = 1)) \Rightarrow (\operatorname{IsPOVM}\left(a \mapsto \operatorname{diagonal}\left(i \mapsto \operatorname{ofReal}\left(p\left(a, i\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.diagonal_povm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let d be any natural dimension and Omega a finite outcome type. Suppose the real weights p(a,i) are nonnegative for every outcome a and coordinate i in Fin d, and sum to one over a at each coordinate. The matrices M(a)=diagonal(i maps to the complex embedding of p(a,i)) form a POVM: each effect is positive semidefinite and their sum is the identity. Empty index types and zero effects are included whenever the hypotheses hold.

**Definition 1.3 (Joint measurements).**

$$\forall d \in \mathbb{N},\; \forall Omega \in Type,\; [\operatorname{Fintype}\left(Omega\right)] \forall Lambda \in Type,\; [\operatorname{Fintype}\left(Lambda\right)] \forall M \in Omega \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall N \in Lambda \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{Compatible}\left(M, N\right) \Leftrightarrow ((\operatorname{IsPOVM}\left(M\right)) \land ((\operatorname{IsPOVM}\left(N\right)) \land (\exists J \in Omega \times Lambda \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{IsPOVM}\left(J\right)) \land ((\forall a \in Omega,\; \sum_{b : Lambda} (J\left((a, b)\right)) = M\left(a\right)) \land (\forall b \in Lambda,\; \sum_{a : Omega} (J\left((a, b)\right)) = N\left(b\right))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.Compatible` (`✓ std3`).

*Citation.* Mohd Asad Siddiqui; Zizhu Wang (2026). *Operational Concealment of Measurement Incompatibility by Quantum Channels: Rank Loss versus Contraction*. DOI: [10.48550/arXiv.2607.11762](https://doi.org/10.48550/arXiv.2607.11762). URL: <https://arxiv.org/abs/2607.11762v2>.

*Commentary.*

Two POVMs with outcome types Omega and Lambda are compatible if a positive normalized family on Omega times Lambda has the two given marginal sums.

**Definition 1.4 (Operational concealment).**

$$\forall din \in \mathbb{N},\; \forall dout \in \mathbb{N},\; \forall E \in \operatorname{MatrixMap}\left(\operatorname{Fin}\left(din\right), \operatorname{Fin}\left(dout\right), \mathbb{C}\right),\; \forall T \in \operatorname{Set}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(din\right), \operatorname{Fin}\left(din\right), \mathbb{C}\right)\right),\; \forall Omega \in Type,\; [\operatorname{Fintype}\left(Omega\right)] \forall Lambda \in Type,\; [\operatorname{Fintype}\left(Lambda\right)] \forall M \in Omega \to \operatorname{Matrix}\left(\operatorname{Fin}\left(dout\right), \operatorname{Fin}\left(dout\right), \mathbb{C}\right),\; \forall N \in Lambda \to \operatorname{Matrix}\left(\operatorname{Fin}\left(dout\right), \operatorname{Fin}\left(dout\right), \mathbb{C}\right),\; \operatorname{Concealed}\left(E, T, M, N\right) \Leftrightarrow (\exists F \in Omega \to \operatorname{Matrix}\left(\operatorname{Fin}\left(dout\right), \operatorname{Fin}\left(dout\right), \mathbb{C}\right),\; \exists G \in Lambda \to \operatorname{Matrix}\left(\operatorname{Fin}\left(dout\right), \operatorname{Fin}\left(dout\right), \mathbb{C}\right),\; (\operatorname{Compatible}\left(F, G\right)) \land ((\forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(din\right), \operatorname{Fin}\left(din\right), \mathbb{C}\right),\; (rho \in T) \Rightarrow (\forall a \in Omega,\; \operatorname{tr}\left((F\left(a\right)) \cdot (E\left(rho\right))\right) = \operatorname{tr}\left((M\left(a\right)) \cdot (E\left(rho\right))\right))) \land (\forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(din\right), \operatorname{Fin}\left(din\right), \mathbb{C}\right),\; (rho \in T) \Rightarrow (\forall b \in Lambda,\; \operatorname{tr}\left((G\left(b\right)) \cdot (E\left(rho\right))\right) = \operatorname{tr}\left((N\left(b\right)) \cdot (E\left(rho\right))\right)))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.Concealed` (`✓ std3`).

*Citation.* Mohd Asad Siddiqui; Zizhu Wang (2026). *Operational Concealment of Measurement Incompatibility by Quantum Channels: Rank Loss versus Contraction*. DOI: [10.48550/arXiv.2607.11762](https://doi.org/10.48550/arXiv.2607.11762). URL: <https://arxiv.org/abs/2607.11762v2>.

*Commentary.*

Let E map input matrices of dimension din to output matrices of dimension dout, and let T be a set of input density matrices. Concealment requires compatible output POVMs F and G with the same outcome types as M and N. Each simulated outcome has the same trace probability as the corresponding original outcome on E(rho), for every rho in T. For a Kraus family K the channel is E(rho)=sum over j of K(j) rho K(j) adjoint.

**Definition 1.5 (Tomographic completeness).**

$$\forall d \in \mathbb{N},\; \forall T \in \operatorname{Set}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right),\; \operatorname{TomographicallyComplete}\left(T\right) \Leftrightarrow ((\forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (rho \in T) \Rightarrow ((\operatorname{PosSemidef}\left(rho\right)) \land (\operatorname{tr}\left(rho\right) = 1))) \land (\operatorname{span}\left(\mathbb{R}, T\right) = \operatorname{HermitianSpace}\left(d\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.TomographicallyComplete` (`✓ std3`).

*Citation.* Mohd Asad Siddiqui; Zizhu Wang (2026). *Operational Concealment of Measurement Incompatibility by Quantum Channels: Rank Loss versus Contraction*. DOI: [10.48550/arXiv.2607.11762](https://doi.org/10.48550/arXiv.2607.11762). URL: <https://arxiv.org/abs/2607.11762v2>.

*Commentary.*

Every member of T is positive semidefinite and has trace one. Its span over the real numbers equals the real vector space of Hermitian matrices. The set of all density matrices has this property: a Hermitian matrix is the difference of two positive semidefinite matrices; each nonzero positive semidefinite matrix is its positive real trace times a density matrix. A positive semidefinite matrix of trace zero is zero.

**Definition 1.6 (The Hermitian adjoint kernel).**

$$\forall din \in \mathbb{N},\; \forall dout \in \mathbb{N},\; \forall E \in \operatorname{MatrixMap}\left(\operatorname{Fin}\left(din\right), \operatorname{Fin}\left(dout\right), \mathbb{C}\right),\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(dout\right), \operatorname{Fin}\left(dout\right), \mathbb{C}\right),\; A \in \operatorname{AdjointKernel}\left(E\right) \Leftrightarrow ((\operatorname{IsHermitian}\left(A\right)) \land (\operatorname{dual}\left(E\right)\left(A\right) = 0))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.AdjointKernel` (`✓ std3`).

*Citation.* Mohd Asad Siddiqui; Zizhu Wang (2026). *Operational Concealment of Measurement Incompatibility by Quantum Channels: Rank Loss versus Contraction*. DOI: [10.48550/arXiv.2607.11762](https://doi.org/10.48550/arXiv.2607.11762). URL: <https://arxiv.org/abs/2607.11762v2>.

*Commentary.*

The trace dual is characterized by tr(E(X)A)=tr(X E adjoint(A)) for every input matrix X and output matrix A. Nondegeneracy and cyclicity of the trace pairing identify the dual of a finite Kraus map with the Heisenberg sum over j of K(j) adjoint A K(j). The kernel here consists only of Hermitian output operators.

**Definition 1.7 (Kernel necessity for concealment equivalence).**

$$claim \Leftrightarrow (\forall din \in \mathbb{N},\; \forall dout \in \mathbb{N},\; \forall kappa \in Type,\; [\operatorname{Fintype}\left(kappa\right)] \forall eta \in Type,\; [\operatorname{Fintype}\left(eta\right)] \forall K \in kappa \to \operatorname{Matrix}\left(\operatorname{Fin}\left(dout\right), \operatorname{Fin}\left(din\right), \mathbb{C}\right),\; \forall L \in eta \to \operatorname{Matrix}\left(\operatorname{Fin}\left(dout\right), \operatorname{Fin}\left(din\right), \mathbb{C}\right),\; (\sum_{j : kappa} ((\operatorname{adjoint}\left(K\left(j\right)\right)) \cdot (K\left(j\right))) = 1) \Rightarrow ((\sum_{j : eta} ((\operatorname{adjoint}\left(L\left(j\right)\right)) \cdot (L\left(j\right))) = 1) \Rightarrow (\forall T \in \operatorname{Set}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(din\right), \operatorname{Fin}\left(din\right), \mathbb{C}\right)\right),\; (\operatorname{TomographicallyComplete}\left(T\right)) \Rightarrow ((\forall Omega \in Type,\; [\operatorname{Fintype}\left(Omega\right)] \forall Lambda \in Type,\; [\operatorname{Fintype}\left(Lambda\right)] \forall M \in Omega \to \operatorname{Matrix}\left(\operatorname{Fin}\left(dout\right), \operatorname{Fin}\left(dout\right), \mathbb{C}\right),\; \forall N \in Lambda \to \operatorname{Matrix}\left(\operatorname{Fin}\left(dout\right), \operatorname{Fin}\left(dout\right), \mathbb{C}\right),\; (\operatorname{IsPOVM}\left(M\right)) \Rightarrow ((\operatorname{IsPOVM}\left(N\right)) \Rightarrow (\operatorname{Concealed}\left(\operatorname{ofKraus}\left(K, K\right), T, M, N\right) \Leftrightarrow (\operatorname{Concealed}\left(\operatorname{ofKraus}\left(L, L\right), T, M, N\right))))) \Rightarrow (\operatorname{AdjointKernel}\left(\operatorname{ofKraus}\left(K, K\right)\right) = \operatorname{AdjointKernel}\left(\operatorname{ofKraus}\left(L, L\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.claim` (`✓ std3`).

*Citation.* Mohd Asad Siddiqui; Zizhu Wang (2026). *Operational Concealment of Measurement Incompatibility by Quantum Channels: Rank Loss versus Contraction*. DOI: [10.48550/arXiv.2607.11762](https://doi.org/10.48550/arXiv.2607.11762). URL: <https://arxiv.org/abs/2607.11762v2>.

*Commentary.*

The assertion quantifies over all finite input and output dimensions, all finite Kraus index types kappa and eta, and all trace-preserving Kraus families K and L with those common dimensions. For every tomographically complete density set T, equality of concealment for every pair of finite outcome types and every pair of POVMs would imply equality of the two Hermitian adjoint kernels. The finite-type hypotheses specify the sums; the Kraus completeness equalities specify trace preservation.

**Theorem 1.8 (A qubit counterexample).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/siddiqui-wang-2026-concealment-kernel-necessity` (refuted) by `D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"siddiqui-wang-2026-concealment-kernel-necessity","declaration_gid":"D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mohd Asad Siddiqui; Zizhu Wang (2026). *Operational Concealment of Measurement Incompatibility by Quantum Channels: Rank Loss versus Contraction*. DOI: [10.48550/arXiv.2607.11762](https://doi.org/10.48550/arXiv.2607.11762). URL: <https://arxiv.org/abs/2607.11762v2>.

*Commentary.*

Take din=dout=2 and T to be all density matrices. The complete dephasing channel D has Kraus operators |0><0| and |1><1|, so D(A)=diag(A00,A11). For arbitrary finite POVMs M and N, put F(a)=diag(M(a)00,M(a)11), G(b)=diag(N(b)00,N(b)11), and J(a,b)=diag(M(a)00 N(b)00,M(a)11 N(b)11). Positive semidefinite effects have nonnegative real diagonal entries. Thus J is positive; normalization of M and N gives normalization of J and both marginal identities. Diagonal outputs give identical trace probabilities for F and M, and for G and N.

The complete depolarization channel R has Kraus operators I/2, X/2, Y/2, Z/2, where Y=iXZ and X,Z are the Pauli matrices. The Kraus completeness sum is I, and R(A)=tr(A)I/2. Put F(a)=tr(M(a))I/2, G(b)=tr(N(b))I/2, and J(a,b)=tr(M(a))tr(N(b))I/4. The traces are nonnegative real numbers and sum to two. These scalar effects and their joint family are positive, normalized, and have the stated marginals. Scalar outputs give the same outcome probabilities as the original effects.

Both constructions hold for arbitrary finite outcome types, so both channels conceal every pair. Yet D adjoint(Z)=Z is nonzero, whereas R adjoint(Z)=0. Their concealment relations coincide and their Hermitian adjoint kernels differ. Each output range is commutative and allows a classical joint simulation; concealment therefore loses the distinction between these two kernels.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.AdjointKernel`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.Compatible`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.Concealed`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.TomographicallyComplete`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.diagonal_povm`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.result`
- Dependency: [D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence](../Information/StabilizerPairLocalUnitaryInequivalence.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation](PositiveFilterTransposeRefutation.md)
- Dependency: [D5/S3/QuantumChannels/CumulantRenyiDataProcessingRefutation](../../QuantumChannels/CumulantRenyiDataProcessingRefutation.md)
