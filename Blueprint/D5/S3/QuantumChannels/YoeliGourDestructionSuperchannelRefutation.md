# Destruction covariance need not be a superchannel fixed set

## Abstract

Qutrit complete dephasing obstructs an exact superchannel fixed-point description of destruction covariance.

**Definition 1.1 (Admissible destruction channels).**

$$\forall d \in \mathbb{N},\; \forall Delta \in \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{IsDestruction}\left(Delta\right) = \left((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{QuantumChannels}.\operatorname{EntanglementAssistedCommunicationValue}.\operatorname{IsChannel}\left(Delta\right)) \land ((\operatorname{LinearMap}.\operatorname{comp}\left(Delta, Delta\right) = Delta) \land (\exists rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{Matrix}.\operatorname{PosDef}\left(rho\right)) \land ((\operatorname{Matrix}.\operatorname{trace}\left(rho\right) = 1) \land (Delta\left(rho\right) = rho))))\right)$$

*Formalization.* `D5/S3/QuantumChannels/YoeliGourDestructionSuperchannelRefutation.IsDestruction` (`✓ std3`).

*Citation.* Goni Yoeli and Gilad Gour (2026). *Instability as a Quantum Resource*. DOI: [10.48550/arXiv.2602.18323](https://doi.org/10.48550/arXiv.2602.18323). URL: <https://arxiv.org/abs/2602.18323v1>.

*Commentary.*

Framework, PDF page 1: "The resource theory of instability therefore considers systems as pairs (A, Δᴬ), where A ≅ ℂᵈ and Δᴬ is an idempotent “destruction” channel." "We assume Δᴬ fixes at least one full-rank state, ensuring the Heisenberg dual Δᴬ* is a faithful conditional expectation (a standard operator-algebraic concept, see Appendix A and [40–46])." IsChannel means completely positive and trace preserving. A full-rank density matrix is represented by Matrix.PosDef together with trace one; the fixed state is quantified explicitly.

**Definition 1.2 (The universal fixed-set assertion).**

$$claim = \left(\forall a \in \mathbb{N},\; (0 < a) \Rightarrow (\forall b \in \mathbb{N},\; (0 < b) \Rightarrow (\forall DeltaA \in \operatorname{MatrixMap}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(a\right), \mathbb{C}\right),\; \forall DeltaB \in \operatorname{MatrixMap}\left(\operatorname{Fin}\left(b\right), \operatorname{Fin}\left(b\right), \mathbb{C}\right),\; (\operatorname{IsDestruction}\left(DeltaA\right)) \Rightarrow ((\operatorname{IsDestruction}\left(DeltaB\right)) \Rightarrow (\exists Theta \in (\operatorname{MatrixMap}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), \mathbb{C}\right)) \to_{\mathbb{C}} (\operatorname{MatrixMap}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), \mathbb{C}\right)),\; (\operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{DalySuperchannelMinimalExtension}.\operatorname{IsQuantumSuperchannel}\left(Theta\right)) \land ((\operatorname{LinearMap}.\operatorname{comp}\left(Theta, Theta\right) = Theta) \land (\forall N \in \operatorname{MatrixMap}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), \mathbb{C}\right),\; (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{QuantumChannels}.\operatorname{EntanglementAssistedCommunicationValue}.\operatorname{IsChannel}\left(N\right)) \Rightarrow ((Theta\left(N\right) = N) \Leftrightarrow (\operatorname{LinearMap}.\operatorname{comp}\left(N, DeltaA\right) = \operatorname{LinearMap}.\operatorname{comp}\left(DeltaB, N\right)))))))))\right)$$

*Formalization.* `D5/S3/QuantumChannels/YoeliGourDestructionSuperchannelRefutation.claim` (`✓ std3`).

*Citation.* Goni Yoeli and Gilad Gour (2026). *Instability as a Quantum Resource*. DOI: [10.48550/arXiv.2602.18323](https://doi.org/10.48550/arXiv.2602.18323). URL: <https://arxiv.org/abs/2602.18323v1>.

*Commentary.*

Open directions, PDF page 5, after Eq. (29): "Moreover, a key open question is whether destruction-covariant channels themselves arise as fixed points of an idempotent superchannel." Framework, PDF page 1, Eq. (1): "In instability theory, we take the free operations between systems A and B to be the destruction-covariant channels 𝒩 obeying" 𝒩ᴬ→ᴮ ∘ Δᴬ = Δᴮ ∘ 𝒩ᴬ→ᴮ. The assertion means exact equality of the fixed CPTP channels with the destruction-covariant CPTP channels, for every pair of admissible nonzero systems. IsQuantumSuperchannel is the existing full-map-space predicate: CP preservation, complete CP preservation with arbitrary auxiliary systems, and TP preservation. Idempotence is equality of the full linear supermap. The dimensions a and b are positive; Fin indices start at zero.

**Theorem 1.3 (A negative answer from qutrit dephasing).**

$$\neg (\forall a \in \mathbb{N},\; (0 < a) \Rightarrow (\forall b \in \mathbb{N},\; (0 < b) \Rightarrow (\forall DeltaA \in \operatorname{MatrixMap}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(a\right), \mathbb{C}\right),\; \forall DeltaB \in \operatorname{MatrixMap}\left(\operatorname{Fin}\left(b\right), \operatorname{Fin}\left(b\right), \mathbb{C}\right),\; (\operatorname{IsDestruction}\left(DeltaA\right)) \Rightarrow ((\operatorname{IsDestruction}\left(DeltaB\right)) \Rightarrow (\exists Theta \in (\operatorname{MatrixMap}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), \mathbb{C}\right)) \to_{\mathbb{C}} (\operatorname{MatrixMap}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), \mathbb{C}\right)),\; (\operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{DalySuperchannelMinimalExtension}.\operatorname{IsQuantumSuperchannel}\left(Theta\right)) \land ((\operatorname{LinearMap}.\operatorname{comp}\left(Theta, Theta\right) = Theta) \land (\forall N \in \operatorname{MatrixMap}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), \mathbb{C}\right),\; (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{QuantumChannels}.\operatorname{EntanglementAssistedCommunicationValue}.\operatorname{IsChannel}\left(N\right)) \Rightarrow ((Theta\left(N\right) = N) \Leftrightarrow (\operatorname{LinearMap}.\operatorname{comp}\left(N, DeltaA\right) = \operatorname{LinearMap}.\operatorname{comp}\left(DeltaB, N\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/YoeliGourDestructionSuperchannelRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/yoeli-gour-destruction-superchannel` (refuted) by `D5/S3/QuantumChannels/YoeliGourDestructionSuperchannelRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"yoeli-gour-destruction-superchannel","declaration_gid":"D5/S3/QuantumChannels/YoeliGourDestructionSuperchannelRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Goni Yoeli and Gilad Gour (2026). *Instability as a Quantum Resource*. DOI: [10.48550/arXiv.2602.18323](https://doi.org/10.48550/arXiv.2602.18323). URL: <https://arxiv.org/abs/2602.18323v1>.

*Commentary.*

Choose both dimensions equal to three and both destruction channels equal to complete dephasing. The depolarizing channel forces the induced completely positive Choi map to be unital. Sixteen normalized Choi vectors of monomial unitaries span the nine-dimensional Choi space and have connected nonzero-overlap graph. Connected-probe rigidity forces the superchannel to be identity. Conjugation by the rational rotation with block ((3/5, −4/5), (4/5, 3/5)) then contradicts exactness: it is CPTP but does not commute with dephasing. The rigidity argument uses no superchannel idempotence and assumes no trace preservation on arbitrary Choi matrices. The equal-dimension qubit case and arbitrary destruction maps are separate questions.

## References

- Truth anchor: `D5/S3/QuantumChannels/YoeliGourDestructionSuperchannelRefutation.IsDestruction`
- Truth anchor: `D5/S3/QuantumChannels/YoeliGourDestructionSuperchannelRefutation.claim`
- Truth anchor: `D5/S3/QuantumChannels/YoeliGourDestructionSuperchannelRefutation.result`
- Dependency: [D5/S3/Quantum/Algebra/CStarSmaleHigherOrder](../Quantum/Algebra/CStarSmaleHigherOrder.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Quantum/Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../Quantum/Foundation/FiniteKrausRepresentation.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Quantum/Foundation/FiniteStateChannel.md)
- Dependency: [D5/S3/Quantum/Matrix/MonomialDiagonalPreserving](../Quantum/Matrix/MonomialDiagonalPreserving.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/CoherenceBreakingAmendment](../Quantum/QuantumChannels/CoherenceBreakingAmendment.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/EntanglementAssistedCommunicationValue](../Quantum/QuantumChannels/EntanglementAssistedCommunicationValue.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/PostprocessedImprovementUnfaithful](../Quantum/QuantumChannels/PostprocessedImprovementUnfaithful.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum](../Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.md)
- Dependency: [D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation](../Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.md)
- Dependency: [D5/S3/Quantum/Reduction/ProbeComponentRigidity](../Quantum/Reduction/ProbeComponentRigidity.md)
- Dependency: [D5/S3/QuantumChannels/ChannelTimeReversalNoGo](ChannelTimeReversalNoGo.md)
- Dependency: [D5/S3/QuantumChannels/DalySuperchannelMinimalExtension](DalySuperchannelMinimalExtension.md)
