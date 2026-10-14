# Weighted multicopy designs need not be optimal

## Abstract

Seven qubit states with three copies outperform every minimal weighted design with the maximally mixed state appended.

**Definition 1.1 (Six qubit preparation vectors).**

$$\operatorname{D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.octVec} = \operatorname{Matrix.vecCons}\left(\operatorname{Matrix.vecCons}\left((1 : \mathbb{C}), \operatorname{Matrix.vecCons}\left(0, \operatorname{Matrix.vecEmpty}\right)\right), \operatorname{Matrix.vecCons}\left(\operatorname{Matrix.vecCons}\left(0, \operatorname{Matrix.vecCons}\left(1, \operatorname{Matrix.vecEmpty}\right)\right), \operatorname{Matrix.vecCons}\left(\operatorname{Matrix.vecCons}\left(1, \operatorname{Matrix.vecCons}\left(1, \operatorname{Matrix.vecEmpty}\right)\right), \operatorname{Matrix.vecCons}\left(\operatorname{Matrix.vecCons}\left(1, \operatorname{Matrix.vecCons}\left(-1, \operatorname{Matrix.vecEmpty}\right)\right), \operatorname{Matrix.vecCons}\left(\operatorname{Matrix.vecCons}\left(1, \operatorname{Matrix.vecCons}\left(\operatorname{Complex.I}, \operatorname{Matrix.vecEmpty}\right)\right), \operatorname{Matrix.vecCons}\left(\operatorname{Matrix.vecCons}\left(1, \operatorname{Matrix.vecCons}\left(-\operatorname{Complex.I}, \operatorname{Matrix.vecEmpty}\right)\right), \operatorname{Matrix.vecEmpty}\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.octVec` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The six vectors are the computational basis vectors and the two eigenvectors of each of the Pauli X and Y matrices. They are unnormalized; their squared norms are 1, 1, 2, 2, 2 and 2, respectively.

**Definition 1.2 (Tensor powers in digit coordinates).**

$$\forall (d : \mathbb{N}), \forall (k : \mathbb{N}), \forall (A : \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \forall (i : \operatorname{Fin}\left(d^{k}\right)), \forall (j : \operatorname{Fin}\left(d^{k}\right)), \operatorname{D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.tensorPow}\left(k, A\right)\left(i, j\right) = \prod_{(t : \operatorname{Fin}\left(k\right))} (A\left(\operatorname{Equiv.symm}\left((\operatorname{finFunctionFinEquiv} : \operatorname{Equiv}\left(\operatorname{Fin}\left(k\right) \to \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d^{k}\right)\right))\right)\left(i\right)\left(t\right), \operatorname{Equiv.symm}\left((\operatorname{finFunctionFinEquiv} : \operatorname{Equiv}\left(\operatorname{Fin}\left(k\right) \to \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d^{k}\right)\right))\right)\left(j\right)\left(t\right)\right))$$

*Formalization.* `D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.tensorPow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The equivalence finFunctionFinEquiv identifies a function Fin k → Fin d with an index in Fin (d^k). Each matrix entry is the product of the k entries selected by the inverse equivalence. This gives tensor powers also when k=0, using the empty product.

**Definition 1.3 (Permutation of tensor factors).**

$$\forall (d : \mathbb{N}), \forall (k : \mathbb{N}), \forall (sigma : \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(k\right)\right)), \forall (i : \operatorname{Fin}\left(d^{k}\right)), \forall (j : \operatorname{Fin}\left(d^{k}\right)), \operatorname{D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.permOp}\left(d, k, sigma\right)\left(i, j\right) = \operatorname{ite}\left(\operatorname{Equiv.symm}\left((\operatorname{finFunctionFinEquiv} : \operatorname{Equiv}\left(\operatorname{Fin}\left(k\right) \to \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d^{k}\right)\right))\right)\left(i\right) = \operatorname{Function.comp}\left(\operatorname{Equiv.symm}\left((\operatorname{finFunctionFinEquiv} : \operatorname{Equiv}\left(\operatorname{Fin}\left(k\right) \to \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d^{k}\right)\right))\right)\left(j\right), sigma\right), (1 : \mathbb{C}), (0 : \mathbb{C})\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.permOp` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A permutation of Fin k induces a permutation matrix on the tensor coordinates. Its row i and column j entry is one precisely when the digit function of i equals the digit function of j composed with the permutation, and zero otherwise.

**Definition 1.4 (The symmetric projector).**

$$\forall (d : \mathbb{N}), \forall (k : \mathbb{N}), \operatorname{D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.PiSym}\left(d, k\right) = \operatorname{HSMul.hSMul}\left(((\operatorname{Nat.cast}\left(\operatorname{Nat.factorial}\left(k\right)\right) : \mathbb{C}))^{-1}, \sum_{(sigma : \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(k\right)\right))} (\operatorname{D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.permOp}\left(d, k, sigma\right))\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.PiSym` (`✓ std3`).

*Citation.* M. Kvashchuk, P. Chernyshova, L. E. A. Porto, T.-A. Ohst, L. B. Vieira, M. T. Quintino (2026). *The most discriminable quantum states in the multicopy regime*. URL: <https://arxiv.org/abs/2604.26927v3>.

*Commentary.*

Equation (8) expresses the symmetric projector as the average of all tensor-factor permutation matrices. The normalization is the inverse of Nat.factorial k cast to the complex numbers; the sum ranges over Equiv.Perm (Fin k).

**Definition 1.5 (Weighted state designs).**

$$\forall (d : \mathbb{N}), \forall (N : \mathbb{N}), \forall (k : \mathbb{N}), \forall (rho : \operatorname{Fin}\left(N\right) \to \operatorname{D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState}\left(\operatorname{Fin}\left(d\right)\right)), \forall (p : \operatorname{Fin}\left(N\right) \to \mathbb{R}), (\operatorname{D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.IsWeightedDesign}\left(k, rho, p\right)) \Leftrightarrow ((\forall (i : \operatorname{Fin}\left(N\right)), 0 \le p\left(i\right)) \land ((\sum_{(i : \operatorname{Fin}\left(N\right))} (p\left(i\right)) = (1 : \mathbb{R})) \land ((\forall (i : \operatorname{Fin}\left(N\right)), (0 < p\left(i\right)) \Rightarrow (\operatorname{D5.S3.Quantum.Foundation.FiniteDiamondDistance.IsPure}\left(rho\left(i\right)\right))) \land (\sum_{(i : \operatorname{Fin}\left(N\right))} (\operatorname{HSMul.hSMul}\left(\operatorname{Complex.ofReal}\left(p\left(i\right)\right), \operatorname{D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.tensorPow}\left(k, (rho\left(i\right)).1\right)\right)) = \operatorname{HSMul.hSMul}\left((\operatorname{Matrix.trace}\left(\operatorname{D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.PiSym}\left(d, k\right)\right))^{-1}, \operatorname{D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.PiSym}\left(d, k\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.IsWeightedDesign` (`✓ std3`).

*Citation.* M. Kvashchuk, P. Chernyshova, L. E. A. Porto, T.-A. Ohst, L. B. Vieira, M. T. Quintino (2026). *The most discriminable quantum states in the multicopy regime*. URL: <https://arxiv.org/abs/2604.26927v3>.

*Commentary.*

Definition 6 requires nonnegative real weights summing to one. A state must be pure whenever its weight is strictly positive; zero-weight states need not be pure. The weighted tensor moment equals the symmetric projector multiplied by the inverse of its complex trace. D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState consists of positive CStarMatrix values of trace one, and D5.S3.Quantum.Foundation.FiniteDiamondDistance.IsPure requires an outer-product representation of the underlying value.

**Definition 1.6 (Existence of a weighted design).**

$$\forall (d : \mathbb{N}), \forall (k : \mathbb{N}), \forall (N : \mathbb{N}), (\operatorname{D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.DesignExists}\left(d, k, N\right)) \Leftrightarrow (\exists (rho : \operatorname{Fin}\left(N\right) \to \operatorname{D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState}\left(\operatorname{Fin}\left(d\right)\right)), \exists (p : \operatorname{Fin}\left(N\right) \to \mathbb{R}), \operatorname{D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.IsWeightedDesign}\left(k, rho, p\right))$$

*Formalization.* `D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.DesignExists` (`✓ std3`).

*Citation.* M. Kvashchuk, P. Chernyshova, L. E. A. Porto, T.-A. Ohst, L. B. Vieira, M. T. Quintino (2026). *The most discriminable quantum states in the multicopy regime*. URL: <https://arxiv.org/abs/2604.26927v3>.

*Commentary.*

The existence condition in §3.3 asks for an N-state family and real weights satisfying Definition 6. Both the family and the weights are existentially quantified.

**Definition 1.7 (The least design size).**

$$\forall (d : \mathbb{N}), \forall (k : \mathbb{N}), \operatorname{D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.Nprime}\left(d, k\right) = \operatorname{sInf}\left((\{(N : \mathbb{N}) \mid \operatorname{D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.DesignExists}\left(d, k, N\right) \} : \operatorname{Set}\left(\mathbb{N}\right))\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.Nprime` (`✓ std3`).

*Citation.* M. Kvashchuk, P. Chernyshova, L. E. A. Porto, T.-A. Ohst, L. B. Vieira, M. T. Quintino (2026). *The most discriminable quantum states in the multicopy regime*. URL: <https://arxiv.org/abs/2604.26927v3>.

*Commentary.*

Section 3.3 defines N′(d,k) as the smallest size admitting a weighted state k-design. Here sInf is taken in the natural numbers. Nat.sInf_def identifies it with the least member of a nonempty set, and Nat.sInf_empty gives zero for the empty set.

**Definition 1.8 (The maximally mixed density state).**

$$\forall (d : \mathbb{N}), \forall (hd : 0 < d), \operatorname{D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.maxMixed}\left(d, hd\right) = \operatorname{D5.S3.Quantum.Divergence.GibbsVariationalIdentity.gibbsState}\left((0 : \operatorname{CStarMatrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \operatorname{IsSelfAdjoint.zero}\left(\operatorname{CStarMatrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.maxMixed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For positive dimension d, maxMixed is D5.S3.Quantum.Divergence.GibbsVariationalIdentity.gibbsState at the zero Hamiltonian, with self-adjointness supplied by IsSelfAdjoint.zero. The index ⟨0,hd⟩ supplies the Nonempty (Fin d) instance. D5.S3.Quantum.Divergence.GibbsVariationalIdentity.gibbs_state_zero identifies its underlying value with the identity scaled by the inverse of the real cast of d, as displayed below.

$$
\forall (d : \mathbb{N}), \forall (hd : 0 < d), (\operatorname{D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.maxMixed}\left(d, hd\right)).1 = \operatorname{CStarMatrix.ofMatrix}\left(\operatorname{HSMul.hSMul}\left(((\operatorname{Nat.cast}\left(d\right) : \mathbb{R}))^{-1}, (1 : \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right))\right)\right)
$$

**Definition 1.9 (Append the maximally mixed state).**

$$\forall (d : \mathbb{N}), \forall (N : \mathbb{N}), \forall (rho : \operatorname{Fin}\left(N\right) \to \operatorname{D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState}\left(\operatorname{Fin}\left(d\right)\right)), \forall (hd : 0 < d), \operatorname{D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.adjoin}\left(rho, hd\right) = \operatorname{Fin.lastCases}\left(\operatorname{D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.maxMixed}\left(d, hd\right), rho\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.adjoin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin.lastCases retains the original states at the first N indices and places the maximally mixed state at the last index of Fin (N+1). The positive-dimension argument supplies the appended density state.

**Definition 1.10 (Multicopy discriminability).**

$$\forall (d : \mathbb{N}), \forall (N : \mathbb{N}), \forall (k : \mathbb{N}), \forall (rho : \operatorname{Fin}\left(N\right) \to \operatorname{D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState}\left(\operatorname{Fin}\left(d\right)\right)), \operatorname{D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.Discr}\left(k, rho\right) = \operatorname{sSup}\left((\{(r : \mathbb{R}) \mid \exists (E : \operatorname{Fin}\left(N\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d^{k}\right), \operatorname{Fin}\left(d^{k}\right), \mathbb{C}\right)), (\operatorname{D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM}\left(E\right)) \land (r = \operatorname{D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation.success}\left((\lambda (i : \operatorname{Fin}\left(N\right)) \mapsto (\operatorname{D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.tensorPow}\left(k, (rho\left(i\right)).1\right))), E\right)) \} : \operatorname{Set}\left(\mathbb{R}\right))\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.Discr` (`✓ std3`).

*Citation.* M. Kvashchuk, P. Chernyshova, L. E. A. Porto, T.-A. Ohst, L. B. Vieira, M. T. Quintino (2026). *The most discriminable quantum states in the multicopy regime*. URL: <https://arxiv.org/abs/2604.26927v3>.

*Commentary.*

Definition 1 in §2 optimizes the equiprobable discrimination success over all N-outcome POVMs on the k-copy space. The definition here uses the real supremum sSup. D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM requires positive semidefinite effects summing to the identity. D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation.success includes the complex scalar 1/(N:ℂ) before taking the real part of each trace, as the following equality shows.

$$
\forall (d : \mathbb{N}), \forall (N : \mathbb{N}), \forall (k : \mathbb{N}), \forall (rho : \operatorname{Fin}\left(N\right) \to \operatorname{D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState}\left(\operatorname{Fin}\left(d\right)\right)), \forall (E : \operatorname{Fin}\left(N\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d^{k}\right), \operatorname{Fin}\left(d^{k}\right), \mathbb{C}\right)), \operatorname{D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation.success}\left((\lambda (i : \operatorname{Fin}\left(N\right)) \mapsto (\operatorname{D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.tensorPow}\left(k, (rho\left(i\right)).1\right))), E\right) = \sum_{(i : \operatorname{Fin}\left(N\right))} (\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(\operatorname{HSMul.hSMul}\left(\frac{(1 : \mathbb{C})}{(\operatorname{Nat.cast}\left(N\right) : \mathbb{C})}, \operatorname{D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.tensorPow}\left(k, (rho\left(i\right)).1\right)\right) \cdot E\left(i\right)\right)\right))
$$

**Definition 1.11 (Optimality of a minimal design with one extra state).**

$$(\operatorname{D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.claim}) \Leftrightarrow (\forall (d : \mathbb{N}), \forall (k : \mathbb{N}), \forall (hd : 0 < d), (0 < k) \Rightarrow (\forall (rho : \operatorname{Fin}\left(\operatorname{D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.Nprime}\left(d, k\right)\right) \to \operatorname{D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState}\left(\operatorname{Fin}\left(d\right)\right)), \forall (p : \operatorname{Fin}\left(\operatorname{D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.Nprime}\left(d, k\right)\right) \to \mathbb{R}), (\operatorname{D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.IsWeightedDesign}\left(k, rho, p\right)) \Rightarrow (\forall (E : \operatorname{Fin}\left(\operatorname{D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.Nprime}\left(d, k\right) + 1\right) \to \operatorname{D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState}\left(\operatorname{Fin}\left(d\right)\right)), \operatorname{D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.Discr}\left(k, E\right) \le \operatorname{D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.Discr}\left(k, \operatorname{D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.adjoin}\left(rho, hd\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.claim` (`✓ std3`).

*Citation.* M. Kvashchuk, P. Chernyshova, L. E. A. Porto, T.-A. Ohst, L. B. Vieira, M. T. Quintino (2026). *The most discriminable quantum states in the multicopy regime*. URL: <https://arxiv.org/abs/2604.26927v3>.

*Commentary.*

Section 11.2 and §12, question 4, ask whether a minimal weighted design combined with the maximally mixed state is optimal. The assertion quantifies over positive dimensions and positive copy counts, every weighted design on N′(d,k) states, and every competing density-state family on N′(d,k)+1 states. The probabilities of the discrimination task are uniform even when the design weights are not.

**Theorem 1.12 (A seven-state qubit counterexample).**

$$\neg (\operatorname{D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/kvashchuk-2026-multicopy-design-refutation` (refuted) by `D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kvashchuk-2026-multicopy-design-refutation","declaration_gid":"D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* M. Kvashchuk, P. Chernyshova, L. E. A. Porto, T.-A. Ohst, L. B. Vieira, M. T. Quintino (2026). *The most discriminable quantum states in the multicopy regime*. URL: <https://arxiv.org/abs/2604.26927v3>.

*Commentary.*

In dimension 2 with three copies, the six octahedral pure states with equal weights form a weighted design. The third-factor partial transpose of the normalized symmetric projector has rank six, whereas each positive-weight pure summand has rank at most one. Thus N′(2,3)=6, and every six-state weighted design has positive weights and pure states. The symmetric projector has trace four. Adding one eighth of its orthogonal complement gives an operator of trace 9/2 that dominates the three-copy state of every pure qubit and the three-copy maximally mixed state. Every six-state weighted design with the maximally mixed state appended therefore has discriminability at most 9/14. A competing family consists of the two computational basis states, the three pure states with normalized vectors (1,ω^j)/√2 for j=0,1,2 and ω=(−1+i√3)/2, and the two diagonal density matrices with diagonals (2/3,1/3) and (1/3,2/3). An explicit seven-outcome POVM has individual success probabilities 51/64, 51/64, 25/32, 25/32, 25/32, 8/27 and 8/27. Their uniform average is 1957/3024, exceeding 9/14 by 13/3024. This gives a negative answer to Kvashchuk and coauthors' question 4 already for qubits.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.DesignExists`
- Truth anchor: `D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.Discr`
- Truth anchor: `D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.IsWeightedDesign`
- Truth anchor: `D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.Nprime`
- Truth anchor: `D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.PiSym`
- Truth anchor: `D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.adjoin`
- Truth anchor: `D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.maxMixed`
- Truth anchor: `D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.octVec`
- Truth anchor: `D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.permOp`
- Truth anchor: `D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.result`
- Truth anchor: `D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.tensorPow`
- Dependency: [D5/S3/Quantum/Divergence/GibbsVariationalIdentity](../Divergence/GibbsVariationalIdentity.md)
- Dependency: [D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation](../Dynamics/KickedIsingNegativityRefutation.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteDiamondDistance](../Foundation/FiniteDiamondDistance.md)
- Dependency: [D5/S3/Quantum/Measurement/EquiprobablePgmActiveSetRefutation](EquiprobablePgmActiveSetRefutation.md)
- Dependency: [D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation](StabilizerPovmMaximalEntanglementRefutation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation](../QuantumChannels/ConcealmentKernelNecessityRefutation.md)
