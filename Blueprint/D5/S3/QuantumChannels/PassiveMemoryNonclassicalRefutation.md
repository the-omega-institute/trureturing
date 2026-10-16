# Passive memory with a nonclassical Gram matrix

## Abstract

In dimension 3, a passive memory implementation exists whose Gram matrix is not classical.

**Definition 1.1 (Complex square matrices).**

$$\forall (\iota : Type*), \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.Mat}\left(\iota\right) = \operatorname{Matrix}\left(\iota, \iota, \mathbb{C}\right)$$

*Formalization.* `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.Mat` (`✓ std3`).

*Citation.* R. Salazar; F. Shahbeigi (2025). *Dephasing noise simulation for coherence-generating devices*. DOI: [10.1088/1402-4896/adda94](https://doi.org/10.1088/1402-4896/adda94). URL: <https://arxiv.org/abs/2403.19247v1>.

*Commentary.*

The operators in Equation (9) are complex matrices. The coordinate type ι is arbitrary; finite coordinate types are specified when sums and channels are used.

**Definition 1.2 (Finite Kraus channels).**

$$\forall (\iota : Type*), [\operatorname{Fintype}\left(\iota\right)], [\operatorname{DecidableEq}\left(\iota\right)], \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.KrausChannel}\left(\iota\right) = \Sigma (n : \mathbb{N}), \{ K : \operatorname{Fin}\left(n\right) \to \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.Mat}\left(\iota\right) // \sum_{(a : \operatorname{Fin}\left(n\right))} (\operatorname{Matrix.conjTranspose}\left(K\left(a\right)\right) \cdot K\left(a\right)) = (1 : \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.Mat}\left(\iota\right)) \}$$

*Formalization.* `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.KrausChannel` (`✓ std3`).

*Citation.* R. Salazar; F. Shahbeigi (2025). *Dephasing noise simulation for coherence-generating devices*. DOI: [10.1088/1402-4896/adda94](https://doi.org/10.1088/1402-4896/adda94). URL: <https://arxiv.org/abs/2403.19247v1>.

*Commentary.*

The channels in Equation (9) have finite Kraus families. The dependent pair records the number n of Kraus operators, and the subtype requires their conjugate-transpose products to sum to the identity matrix.

**Definition 1.3 (Action of a Kraus channel).**

$$\forall (\iota : Type*), [\operatorname{Fintype}\left(\iota\right)], [\operatorname{DecidableEq}\left(\iota\right)], \forall (E : \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.KrausChannel}\left(\iota\right)), \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.act}\left(E\right) = \operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of}_{kraus}\left(((E).2).1, ((E).2).1\right)$$

*Formalization.* `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.act` (`✓ std3`).

*Citation.* R. Salazar; F. Shahbeigi (2025). *Dephasing noise simulation for coherence-generating devices*. DOI: [10.1088/1402-4896/adda94](https://doi.org/10.1088/1402-4896/adda94). URL: <https://arxiv.org/abs/2403.19247v1>.

*Commentary.*

Equation (9) uses the channel action. D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus applies the family on the left and its conjugate transpose on the right; the two family arguments here are both E.2.1.

**Definition 1.4 (The matrix of a density state).**

$$\forall (\iota : Type*), [\operatorname{Fintype}\left(\iota\right)], [\operatorname{DecidableEq}\left(\iota\right)], \forall (\rho : \operatorname{D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState}\left(\iota\right)), \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.stateMatrix}\left(\rho\right) = \operatorname{Equiv.symm}\left(\operatorname{CStarMatrix.ofMatrix}\right)\left(((\rho).1 : \operatorname{CStarMatrix}\left(\iota, \iota, \mathbb{C}\right))\right)$$

*Formalization.* `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.stateMatrix` (`✓ std3`).

*Citation.* R. Salazar; F. Shahbeigi (2025). *Dephasing noise simulation for coherence-generating devices*. DOI: [10.1088/1402-4896/adda94](https://doi.org/10.1088/1402-4896/adda94). URL: <https://arxiv.org/abs/2403.19247v1>.

*Commentary.*

The states in Equation (9) are positive matrices of trace one. D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState uses CStarMatrix coordinates. Applying Equiv.symm to CStarMatrix.ofMatrix converts the underlying value ρ.1 to an ordinary complex matrix.

**Definition 1.5 (Append the initial memory).**

$$\forall (d : \mathbb{N}), \forall (r : \mathbb{N}), \forall (\tau : \operatorname{D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState}\left(\operatorname{Fin}\left(r\right)\right)), \forall (A : \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.Mat}\left(\operatorname{Fin}\left(d\right)\right)), (\operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.appendMemory}\left(\tau\right) : \operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap}\left(\operatorname{Fin}\left(d\right), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right)), \mathbb{C}\right))\left(A\right) = \operatorname{Matrix.kronecker}\left(A, \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.stateMatrix}\left(\tau\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.appendMemory` (`✓ std3`).

*Citation.* R. Salazar; F. Shahbeigi (2025). *Dephasing noise simulation for coherence-generating devices*. DOI: [10.1088/1402-4896/adda94](https://doi.org/10.1088/1402-4896/adda94). URL: <https://arxiv.org/abs/2403.19247v1>.

*Commentary.*

Equation (9) begins by tensoring an input matrix with the fixed memory state τ. Matrix.kronecker puts the system coordinate first and the memory coordinate second.

**Definition 1.6 (Discard the final memory).**

$$\forall (d : \mathbb{N}), \forall (r : \mathbb{N}), \forall (A : \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.Mat}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right))\right)), (\operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.discardMemory} : \operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right)), \operatorname{Fin}\left(d\right), \mathbb{C}\right))\left(A\right) = \operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight}\left(A\right)$$

*Formalization.* `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.discardMemory` (`✓ std3`).

*Citation.* R. Salazar; F. Shahbeigi (2025). *Dephasing noise simulation for coherence-generating devices*. DOI: [10.1088/1402-4896/adda94](https://doi.org/10.1088/1402-4896/adda94). URL: <https://arxiv.org/abs/2403.19247v1>.

*Commentary.*

Equation (9) ends by tracing out the memory. D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight sums the diagonal entries in the second coordinate and retains the system matrix.

**Definition 1.7 (The implemented channel).**

$$\forall (d : \mathbb{N}), \forall (r : \mathbb{N}), \forall (\tau : \operatorname{D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState}\left(\operatorname{Fin}\left(r\right)\right)), \forall (Nen : \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.KrausChannel}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right))\right)), \forall (Nde : \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.KrausChannel}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right))\right)), \forall (E : \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.KrausChannel}\left(\operatorname{Fin}\left(d\right)\right)), \forall (A : \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.Mat}\left(\operatorname{Fin}\left(d\right)\right)), \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.implemented}\left(\tau, Nen, Nde, E\right)\left(A\right) = \operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight}\left(\operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.act}\left(Nde\right)\left(\operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.kron}\left(\operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.act}\left(E\right), (\operatorname{LinearMap.id} : \operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), \mathbb{C}\right))\right)\left(\operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.act}\left(Nen\right)\left(\operatorname{Matrix.kronecker}\left(A, \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.stateMatrix}\left(\tau\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.implemented` (`✓ std3`).

*Citation.* R. Salazar; F. Shahbeigi (2025). *Dephasing noise simulation for coherence-generating devices*. DOI: [10.1088/1402-4896/adda94](https://doi.org/10.1088/1402-4896/adda94). URL: <https://arxiv.org/abs/2403.19247v1>.

*Commentary.*

Equation (9) first appends τ, applies the encoding channel Nen, applies E to the system while leaving the memory unchanged, applies the decoding channel Nde, and traces out the memory. D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.kron is the tensor product of the two linear maps.

**Definition 1.8 (Normalized output-first Choi matrix).**

$$\forall (d : \mathbb{N}), \forall (F : \operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.choi}\left(d, F\right) = \operatorname{HSMul.hSMul}\left((\operatorname{Nat.cast}\left(d\right) : \mathbb{C})^{-1}, \operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.choi}_{matrix}\left(F\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.choi` (`✓ std3`).

*Citation.* R. Salazar; F. Shahbeigi (2025). *Dephasing noise simulation for coherence-generating devices*. DOI: [10.1088/1402-4896/adda94](https://doi.org/10.1088/1402-4896/adda94). URL: <https://arxiv.org/abs/2403.19247v1>.

*Commentary.*

Equation (2) uses a normalized maximally entangled input. The definition scales D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.choi_matrix F by the inverse of the complex cast of d. Accordingly, the entry at row (i,j) and column (k,l) is the (i,k) entry of F applied to Matrix.single j l 1, multiplied by that inverse. The first coordinate is the output coordinate. The definition also accepts d=0.

**Definition 1.9 (Gram matrices).**

$$\forall (\iota : Type*), \forall (C : \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.Mat}\left(\iota\right)), (\operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.Gram}\left(C\right)) \Leftrightarrow ((\operatorname{Matrix.PosSemidef}\left(C\right)) \land (\forall (i : \iota), C\left(i, i\right) = (1 : \mathbb{C})))$$

*Formalization.* `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.Gram` (`✓ std3`).

*Citation.* R. Salazar; F. Shahbeigi (2025). *Dephasing noise simulation for coherence-generating devices*. DOI: [10.1088/1402-4896/adda94](https://doi.org/10.1088/1402-4896/adda94). URL: <https://arxiv.org/abs/2403.19247v1>.

*Commentary.*

The Gram matrices in Equations (13) and (19) are positive semidefinite complex matrices with every diagonal entry equal to one.

**Definition 1.10 (Equal diagonal blocks).**

$$\forall (d : \mathbb{N}), \forall (C : \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.Mat}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right))\right)), (\operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.DephasingGram}\left(C\right)) \Leftrightarrow ((\operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.Gram}\left(C\right)) \land (\forall (i : \operatorname{Fin}\left(d\right)), \forall (k : \operatorname{Fin}\left(d\right)), \forall (j : \operatorname{Fin}\left(d\right)), \forall (l : \operatorname{Fin}\left(d\right)), C\left((i, j), (i, l)\right) = C\left((k, j), (k, l)\right)))$$

*Formalization.* `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.DephasingGram` (`✓ std3`).

*Citation.* R. Salazar; F. Shahbeigi (2025). *Dephasing noise simulation for coherence-generating devices*. DOI: [10.1088/1402-4896/adda94](https://doi.org/10.1088/1402-4896/adda94). URL: <https://arxiv.org/abs/2403.19247v1>.

*Commentary.*

Equation (13) requires all diagonal blocks of the Gram matrix to agree: for every i,k,j,l, the entry C((i,j),(i,l)) equals C((k,j),(k,l)).

**Definition 1.11 (Passive memory).**

$$\forall (d : \mathbb{N}), \forall (r : \mathbb{N}), \forall (\tau : \operatorname{D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState}\left(\operatorname{Fin}\left(r\right)\right)), \forall (Nen : \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.KrausChannel}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right))\right)), (\operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.Passive}\left(\tau, Nen\right)) \Leftrightarrow (\forall (\rho : \operatorname{D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState}\left(\operatorname{Fin}\left(d\right)\right)), \forall (\sigma : \operatorname{D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState}\left(\operatorname{Fin}\left(d\right)\right)), \operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft}\left(\operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.act}\left(Nen\right)\left(\operatorname{Matrix.kronecker}\left(\operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.stateMatrix}\left(\rho\right), \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.stateMatrix}\left(\tau\right)\right)\right)\right) = \operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft}\left(\operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.act}\left(Nen\right)\left(\operatorname{Matrix.kronecker}\left(\operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.stateMatrix}\left(\sigma\right), \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.stateMatrix}\left(\tau\right)\right)\right)\right))$$

*Formalization.* `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.Passive` (`✓ std3`).

*Citation.* R. Salazar; F. Shahbeigi (2025). *Dephasing noise simulation for coherence-generating devices*. DOI: [10.1088/1402-4896/adda94](https://doi.org/10.1088/1402-4896/adda94). URL: <https://arxiv.org/abs/2403.19247v1>.

*Commentary.*

Definition 2 and Equation (29) require the memory marginal after encoding to be independent of the input state. Equality for every pair of density inputs ρ and σ expresses that independence. D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft traces out the system coordinate.

**Definition 1.12 (Classical Gram matrices).**

$$\forall (d : \mathbb{N}), \forall (C : \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.Mat}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right))\right)), (\operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.ClassicalGram}\left(C\right)) \Leftrightarrow (\exists (n : \mathbb{N}), \exists (q : \operatorname{Fin}\left(n\right) \to \mathbb{R}), \exists (P : \operatorname{Fin}\left(n\right) \to \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.Mat}\left(\operatorname{Fin}\left(d\right)\right)), \exists (Q : \operatorname{Fin}\left(n\right) \to \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.Mat}\left(\operatorname{Fin}\left(d\right)\right)), (\forall (a : \operatorname{Fin}\left(n\right)), 0 \le q\left(a\right)) \land ((\sum_{(a : \operatorname{Fin}\left(n\right))} (q\left(a\right)) = (1 : \mathbb{R})) \land ((\forall (a : \operatorname{Fin}\left(n\right)), (\operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.Gram}\left(P\left(a\right)\right)) \land (\operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.Gram}\left(Q\left(a\right)\right))) \land (C = \sum_{(a : \operatorname{Fin}\left(n\right))} (\operatorname{HSMul.hSMul}\left(q\left(a\right), \operatorname{Matrix.kronecker}\left(P\left(a\right), Q\left(a\right)\right)\right))))))$$

*Formalization.* `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.ClassicalGram` (`✓ std3`).

*Citation.* R. Salazar; F. Shahbeigi (2025). *Dephasing noise simulation for coherence-generating devices*. DOI: [10.1088/1402-4896/adda94](https://doi.org/10.1088/1402-4896/adda94). URL: <https://arxiv.org/abs/2403.19247v1>.

*Commentary.*

Proposition 1(ii) describes classical memory by a finite convex combination of Kronecker products of Gram matrices. The weights q are real and nonnegative, sum to one, and act by scalar multiplication on the complex matrices. Each P(a) and Q(a) has unit diagonal and is positive semidefinite.

**Definition 1.13 (Implementation of a dephasing Gram matrix).**

$$\forall (d : \mathbb{N}), \forall (r : \mathbb{N}), \forall (\tau : \operatorname{D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState}\left(\operatorname{Fin}\left(r\right)\right)), \forall (Nen : \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.KrausChannel}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right))\right)), \forall (Nde : \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.KrausChannel}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right))\right)), \forall (C : \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.Mat}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right))\right)), (\operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.Implements}\left(\tau, Nen, Nde, C\right)) \Leftrightarrow ((\operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.DephasingGram}\left(C\right)) \land (\forall (E : \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.KrausChannel}\left(\operatorname{Fin}\left(d\right)\right)), \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.choi}\left(d, \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.implemented}\left(\tau, Nen, Nde, E\right)\right) = \operatorname{Matrix.hadamard}\left(C, \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.choi}\left(d, \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.act}\left(E\right)\right)\right)))$$

*Formalization.* `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.Implements` (`✓ std3`).

*Citation.* R. Salazar; F. Shahbeigi (2025). *Dephasing noise simulation for coherence-generating devices*. DOI: [10.1088/1402-4896/adda94](https://doi.org/10.1088/1402-4896/adda94). URL: <https://arxiv.org/abs/2403.19247v1>.

*Commentary.*

Equations (13) and (19) combine the equal diagonal-block condition with the channel identity: for every Kraus channel E, the normalized Choi matrix of the implementation is Matrix.hadamard C applied to the normalized Choi matrix of E. Matrix.hadamard is entrywise multiplication.

**Definition 1.14 (Passive memory and classical simulation).**

$$(\operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.claim}) \Leftrightarrow (\forall (d : \mathbb{N}), \forall (r : \mathbb{N}), (0 < d) \Rightarrow ((0 < r) \Rightarrow (\forall (\tau : \operatorname{D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState}\left(\operatorname{Fin}\left(r\right)\right)), \forall (Nen : \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.KrausChannel}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right))\right)), \forall (Nde : \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.KrausChannel}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right))\right)), \forall (C : \operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.Mat}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right))\right)), (\operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.Implements}\left(\tau, Nen, Nde, C\right)) \Rightarrow ((\operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.Passive}\left(\tau, Nen\right)) \Rightarrow (\operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.ClassicalGram}\left(C\right))))))$$

*Formalization.* `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.claim` (`✓ std3`).

*Citation.* R. Salazar; F. Shahbeigi (2025). *Dephasing noise simulation for coherence-generating devices*. DOI: [10.1088/1402-4896/adda94](https://doi.org/10.1088/1402-4896/adda94). URL: <https://arxiv.org/abs/2403.19247v1>.

*Commentary.*

Section V.C asks whether the equivalence with classical memory proved for qubits extends to every dimension. The assertion here quantifies over positive system and finite memory dimensions, every memory density state, every encoding and decoding Kraus channel, and every Gram matrix implemented as in Equations (9), (13) and (19). It asserts that a passive memory always gives the classical decomposition of Proposition 1(ii).

**Theorem 1.15 (A passive memory need not give a classical Gram matrix).**

$$\neg (\operatorname{D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/salazar-shahbeigi-2025-passive-memory-refutation` (refuted) by `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"salazar-shahbeigi-2025-passive-memory-refutation","declaration_gid":"D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. Salazar; F. Shahbeigi (2025). *Dephasing noise simulation for coherence-generating devices*. DOI: [10.1088/1402-4896/adda94](https://doi.org/10.1088/1402-4896/adda94). URL: <https://arxiv.org/abs/2403.19247v1>.

*Commentary.*

For a system of dimension 3 and a memory of dimension 2, take the memory state to be one half of the identity. Use the same block diagonal unitary for encoding and decoding, with diagonal blocks the identity, D5.S3.Quantum.FiniteDimensional.qubitX and D5.S3.Quantum.FiniteDimensional.qubitZ. The memory marginal remains equal to its initial state for every density input. The resulting Gram matrix has equal diagonal blocks and gives the required Choi identity for every Kraus channel. Every classical Gram matrix has a positive semidefinite partial transpose in the second coordinate. Here its principal block on (0,0), (1,1), (2,2) has rows (1,1,1), (1,1,−1), (1,−1,1). Its quadratic form at (−1,1,1) equals −3, so the Gram matrix is not classical. This gives a negative answer to Salazar and Shahbeigi's question in §V.C.

## References

- Truth anchor: `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.ClassicalGram`
- Truth anchor: `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.DephasingGram`
- Truth anchor: `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.Gram`
- Truth anchor: `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.Implements`
- Truth anchor: `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.KrausChannel`
- Truth anchor: `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.Mat`
- Truth anchor: `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.Passive`
- Truth anchor: `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.act`
- Truth anchor: `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.appendMemory`
- Truth anchor: `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.choi`
- Truth anchor: `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.claim`
- Truth anchor: `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.discardMemory`
- Truth anchor: `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.implemented`
- Truth anchor: `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.result`
- Truth anchor: `D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.stateMatrix`
- Dependency: [D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction](../Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction.md)
- Dependency: [D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation](../Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../Quantum/Foundation/FiniteKrausRepresentation.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Quantum/Information/PartialTraceMutualInformation.md)
