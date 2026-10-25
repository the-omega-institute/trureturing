# Projective tests do not characterize channel compatibility

## Abstract

Every pair of projective tests is compatible for a qubit channel that has no joint extension with itself.

**Definition 1.1 (The adjoint image of a basis measurement).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(\phi: \operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\forall \left(U: \operatorname{Subtype}\left(\lambda \left(x: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right) \mapsto \left(x \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.QuantumChannels.ProjectiveTestChannelCompatibilityRefutation.basisPOVM}\left(\phi, U\right): \left(\operatorname{Fin}\left(d\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right) = \lambda \left(i: \operatorname{Fin}\left(d\right)\right) \mapsto \left(\left(\operatorname{DFunLike.coe}\left(\operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.dual}\left(\phi\right)\right)\right)\left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.measurementProjector}\left(U, i\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ProjectiveTestChannelCompatibilityRefutation.basisPOVM` (`✓ std3`).

*Citation.* Qing-Hua Zhang; Ion Nechita (2022). *A Fisher information-based incompatibility criterion for quantum channels*. DOI: [10.3390/e24060805](https://doi.org/10.3390/e24060805). URL: <https://arxiv.org/abs/2204.09963v1>.

*Commentary.*

The columns of the unitary matrix U form an orthonormal basis. For each i, apply the trace dual of the complex linear map φ to the rank-one projector onto column i. These are the projective-test effects in article.tex, lines 239-241 and 263-264. The definition applies to every complex linear matrix map; complete positivity and trace preservation are imposed separately when these effects are used as a POVM.

**Definition 1.2 (A joint channel with two prescribed marginals).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(\phi: \operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\forall \left(\psi: \operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.QuantumChannels.ProjectiveTestChannelCompatibilityRefutation.ChannelCompatible}\left(\phi, \psi\right)\right) \Leftrightarrow \left(\exists \left(J: \operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap}\left(\operatorname{Fin}\left(d\right), \left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation.IsCPTP}\left(J\right)\right) \land \left(\left(\forall \left(X: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight}\left(\left(\operatorname{DFunLike.coe}\left(J\right)\right)\left(X\right)\right) = \left(\operatorname{DFunLike.coe}\left(\phi\right)\right)\left(X\right)\right)\right) \land \left(\forall \left(X: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft}\left(\left(\operatorname{DFunLike.coe}\left(J\right)\right)\left(X\right)\right) = \left(\operatorname{DFunLike.coe}\left(\psi\right)\right)\left(X\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ProjectiveTestChannelCompatibilityRefutation.ChannelCompatible` (`✓ std3`).

*Citation.* Qing-Hua Zhang; Ion Nechita (2022). *A Fisher information-based incompatibility criterion for quantum channels*. DOI: [10.3390/e24060805](https://doi.org/10.3390/e24060805). URL: <https://arxiv.org/abs/2204.09963v1>.

*Commentary.*

A joint completely positive trace-preserving map sends an input matrix to a matrix on the product of the two output spaces. Tracing out the right output gives φ, and tracing out the left output gives ψ, on every complex input matrix. This is the equal-output-dimension case of the channel compatibility definition in article.tex, lines 138-146. The predicate requires the joint map to be a channel; it places no separate channel hypotheses on φ and ψ.

**Definition 1.3 (The proposed converse from projective tests).**

$$\left(\operatorname{D5.S3.Quantum.QuantumChannels.ProjectiveTestChannelCompatibilityRefutation.claim}\right) \Leftrightarrow \left(\forall \left(d: \mathbb{N}\right), \left(\forall \left(\phi: \operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\forall \left(\psi: \operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation.IsCPTP}\left(\phi\right)\right) \to \left(\left(\operatorname{D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation.IsCPTP}\left(\psi\right)\right) \to \left(\left(\forall \left(U: \operatorname{Subtype}\left(\lambda \left(x: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right) \mapsto \left(x \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right)\right), \left(\forall \left(V: \operatorname{Subtype}\left(\lambda \left(x: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right) \mapsto \left(x \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right)\right), \left(\operatorname{D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.Compatible}\left(\operatorname{D5.S3.Quantum.QuantumChannels.ProjectiveTestChannelCompatibilityRefutation.basisPOVM}\left(\phi, U\right), \operatorname{D5.S3.Quantum.QuantumChannels.ProjectiveTestChannelCompatibilityRefutation.basisPOVM}\left(\psi, V\right)\right)\right)\right)\right) \to \left(\operatorname{D5.S3.Quantum.QuantumChannels.ProjectiveTestChannelCompatibilityRefutation.ChannelCompatible}\left(\phi, \psi\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ProjectiveTestChannelCompatibilityRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Qing-Hua Zhang; Ion Nechita (2022). *A Fisher information-based incompatibility criterion for quantum channels*. DOI: [10.3390/e24060805](https://doi.org/10.3390/e24060805). URL: <https://arxiv.org/abs/2204.09963v1>.

*Commentary.*

For every natural dimension d and every two completely positive trace-preserving maps φ and ψ, suppose that every pair of unitary bases gives compatible adjoint-image POVMs. Compatibility of POVMs means that a positive normalized family on the product outcome set has the two given families as its marginals, as in article.tex, lines 192-199. The assertion is that φ and ψ must then have a joint channel. This expresses the conjecture in article.tex, lines 261-266, using unitaries to parameterize bases. The displayed quantifier also includes dimension zero; the counterexample has dimension two.

**Theorem 1.4 (A depolarizing qubit counterexample).**

$$\neg \left(\operatorname{D5.S3.Quantum.QuantumChannels.ProjectiveTestChannelCompatibilityRefutation.claim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/ProjectiveTestChannelCompatibilityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhang-nechita-2022-projective-test-channel-compatibility-refutation` (refuted) by `D5/S3/Quantum/QuantumChannels/ProjectiveTestChannelCompatibilityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhang-nechita-2022-projective-test-channel-compatibility-refutation","declaration_gid":"D5/S3/Quantum/QuantumChannels/ProjectiveTestChannelCompatibilityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Qing-Hua Zhang; Ion Nechita (2022). *A Fisher information-based incompatibility criterion for quantum channels*. DOI: [10.3390/e24060805](https://doi.org/10.3390/e24060805). URL: <https://arxiv.org/abs/2204.09963v1>.

*Commentary.*

Consider the qubit map φ(X) = (7/10)X + (3/20)tr(X)I. Its Pauli representation has probabilities 31/40, 3/40, 3/40 and 3/40. They are nonnegative and sum to one, so φ is completely positive and trace preserving. Cyclicity of the trace pairing shows that its trace dual equals φ.

For arbitrary unitary bases U and V, let Eₐ and Fᵦ be their rank-one projectors. Each projector is Hermitian, has trace one and squares to itself; each pair sums to I. Thus Aₐ = 2Eₐ − I and Bᵦ = 2Fᵦ − I are traceless Hermitian matrices that square to I, and each centered pair sums to zero. Any two traceless two-by-two matrices A and B satisfy AB + BA = tr(AB)I, by expanding their entries and eliminating the second diagonal entries.

Define the four joint effects Gₐᵦ = ((1 + (49/200)tr(AₐBᵦ))I + (7/10)(Aₐ + Bᵦ))/4. To prove positivity, fix a and b and write A = Aₐ, B = Bᵦ and K = A + B. The anticommutator identity gives K² = (2 + tr(AB))I. Since K is Hermitian, K² is positive semidefinite; a diagonal entry therefore shows that tr(AB) is real and at least −2. Put τ = Re(tr(AB)), α = 1 + (49/200)τ and c = 1/50 + (2401/40000)τ². Then α and c are strictly positive, and c = α² − (49/100)(2 + τ). For the Hermitian matrix H = αI + (7/10)K, expansion gives H*H + cI = 2αH, where the star denotes conjugate transpose. Consequently H = (H*H + cI)/(2α) is positive semidefinite, and Gₐᵦ = H/4 is positive semidefinite.

Summing over b cancels the centered B terms and the mixed trace terms, leaving sum over b of Gₐᵦ = φ(Eₐ). Cyclicity of trace and exchange of A and B give sum over a of Gₐᵦ = φ(Fᵦ). Summing again gives I. The marginals are themselves positive semidefinite and normalized, so the four effects form a joint POVM for the two adjoint-image measurements. This holds for every U and V.

Now suppose that a joint channel J for φ and itself exists. Order its Choi indices as ((a,b),r), with a and b the two output indices and r the reference index. Its normalized Choi matrix R has entries R(((a,b),r),((c,d),s)) = J(|r><s|)((a,b),(c,d))/2. Complete positivity makes R positive semidefinite. Trace preservation gives tr(R) = (tr(J(|0><0|)) + tr(J(|1><1|)))/2 = 1.

Let S be the Bell projection on the first output and reference, tensored with the identity on the second output, and let T be the corresponding projection for the second output and reference. The Bell vector is (|00> + |11>)/√2. Expanding the two partial-trace equalities on the matrix units gives tr(RS) = (sum over r,s,b of J(|r><s|)((r,b),(s,b)))/4 = (sum over r,s of φ(|r><s|)(r,s))/4 = 31/40. The other marginal gives tr(RT) = 31/40 in the same way.

The matrix (3/2)I − S − T is positive semidefinite by an explicit Gram decomposition. Write eₐᵦᵣ for the coordinate row with index ((a,b),r). Let C have the four rows e₀₀₀ − e₀₁₁ − e₁₀₁, e₀₁₁ − e₁₀₁, e₁₁₁ − e₀₁₀ − e₁₀₀ and e₀₁₀ − e₁₀₀. Let D be diagonal with entry 3/2 at ((0,0),1) and ((1,1),0), and zero elsewhere. Entrywise expansion gives (3/2)I − S − T = C*C/2 + D. Both summands are positive semidefinite.

The trace of the product of two positive semidefinite matrices is nonnegative. Applying this to R and (3/2)I − S − T gives 0 ≤ (3/2)tr(R) − tr(RS) − tr(RT) = 3/2 − 31/40 − 31/40 = −1/20, a contradiction. Thus φ has no joint channel with itself. Applying claim in dimension two to φ twice would provide just such a joint channel, because both maps are channels and all their projective-test pairs have the joint POVMs above. Therefore claim is false.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/ProjectiveTestChannelCompatibilityRefutation.ChannelCompatible`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ProjectiveTestChannelCompatibilityRefutation.basisPOVM`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ProjectiveTestChannelCompatibilityRefutation.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ProjectiveTestChannelCompatibilityRefutation.result`
- Dependency: [D5/S3/Divergence/CoherenceL1RelativeEntropyBound](../../Divergence/CoherenceL1RelativeEntropyBound.md)
- Dependency: [D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation](../Decoherence/DephasingTwoClassicalityBlockRefutation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation](ChannelAssemblageLOSRRefutation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation](ConcealmentKernelNecessityRefutation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound](TracePreservingEigenvalueBound.md)
- Dependency: [D5/S3/QuantumChannels/PurelyNonUnitalEternalNonMarkovianity](../../QuantumChannels/PurelyNonUnitalEternalNonMarkovianity.md)
