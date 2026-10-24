# ChannelTimeReversalNoGo

## Abstract

Randomisation and complete positivity obstruct reversal of every unitary channel.

**Definition 1.1 (Symmetries of the channel set).**

$$\forall d \in \mathbb{N},\; \forall S \in \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right) \to \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{IsChannelSymmetry}\left(S\right) = \left((\operatorname{Set}.\operatorname{BijOn}\left(S, \{Phi: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right) \mid \operatorname{IsCPTP}\left(Phi\right)\}, \{Phi: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right) \mid \operatorname{IsCPTP}\left(Phi\right)\}\right)) \land (\forall Phi \in \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall Psi \in \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{IsCPTP}\left(Phi\right)) \Rightarrow ((\operatorname{IsCPTP}\left(Psi\right)) \Rightarrow (\forall p \in \mathbb{R},\; (0 \le p) \Rightarrow ((p \le 1) \Rightarrow (S\left(((p: \mathbb{C})) \cdot (Phi) + (((1 - p: \mathbb{R}): \mathbb{C})) \cdot (Psi)\right) = ((p: \mathbb{C})) \cdot (S\left(Phi\right)) + (((1 - p: \mathbb{R}): \mathbb{C})) \cdot (S\left(Psi\right)))))))\right)$$

*Formalization.* `D5/S3/QuantumChannels/ChannelTimeReversalNoGo.IsChannelSymmetry` (`✓ std3`).

*Citation.* Giulio Chiribella and Erik Aurell and Karol Życzkowski (2021). *Symmetries of quantum evolutions*. DOI: [10.1103/PhysRevResearch.3.033028](https://doi.org/10.1103/PhysRevResearch.3.033028). URL: <https://arxiv.org/abs/2101.04962>.

*Commentary.*

Definition 3, PDF page 5: "A symmetry transformation from the operation space Op(Hin , Hout ) to the operation space Op(Kin , Kout ) (an operation space symmetry, for short) is a bijective transformation S : Op(Hin , Hout ) → Op(Kin , Kout )" that "is consistent with randomisations, namely S(p Q + (1−p) R) = p S(Q)+(1−p) S(R), for every pair of quantum operations Q and R, and for every probability p ∈ [0, 1]". On channels the null-operation requirement has no instance. Here Set.BijOn states bijectivity on the set defined by IsCPTP, and the second conjunct states the complete binary randomisation identity for every real probability in [0,1].

**Definition 1.2 (Conjugation by a matrix).**

$$\forall d \in \mathbb{N},\; \forall U \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{unitaryChannel}\left(U\right) = (\operatorname{LinearMap}.\operatorname{mulRight}\left(\mathbb{C}, \operatorname{star}\left(U\right)\right)) \circ_{l} (\operatorname{LinearMap}.\operatorname{mulLeft}\left(\mathbb{C}, U\right))$$

*Formalization.* `D5/S3/QuantumChannels/ChannelTimeReversalNoGo.unitaryChannel` (`✓ std3`).

*Citation.* Giulio Chiribella and Erik Aurell and Karol Życzkowski (2021). *Symmetries of quantum evolutions*. DOI: [10.1103/PhysRevResearch.3.033028](https://doi.org/10.1103/PhysRevResearch.3.033028). URL: <https://arxiv.org/abs/2101.04962>.

*Commentary.*

For every natural dimension d and every complex d by d matrix U, unitaryChannel U is LinearMap.mulRight ℂ (star U) after LinearMap.mulLeft ℂ U. It sends X to U X (star U). For unitary U this is a completely positive trace-preserving map.

**Definition 1.3 (No time reversal on all channels).**

$$claim = \left(\forall d \in \mathbb{N},\; (2 \le d) \Rightarrow (\forall S \in \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right) \to \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{IsChannelSymmetry}\left(S\right)) \Rightarrow ((\neg (\forall U \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (U \in \operatorname{Matrix}.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)) \Rightarrow (S\left(\operatorname{unitaryChannel}\left(U\right)\right) = \operatorname{unitaryChannel}\left(\operatorname{star}\left(U\right)\right)))) \land (\neg (\forall U \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (U \in \operatorname{Matrix}.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)) \Rightarrow (S\left(\operatorname{unitaryChannel}\left(U\right)\right) = \operatorname{unitaryChannel}\left(\operatorname{Matrix}.\operatorname{transpose}\left(U\right)\right))))))\right)$$

*Formalization.* `D5/S3/QuantumChannels/ChannelTimeReversalNoGo.claim` (`✓ std3`).

*Citation.* Giulio Chiribella and Erik Aurell and Karol Życzkowski (2021). *Symmetries of quantum evolutions*. DOI: [10.1103/PhysRevResearch.3.033028](https://doi.org/10.1103/PhysRevResearch.3.033028). URL: <https://arxiv.org/abs/2101.04962>.

*Commentary.*

Section V.B, PDF page 7: "We conjecture that this assumption can be lifted, and that the no-go theorem to time reversal applies also to symmetries of the set of quantum channels." The dimension d ranges over every natural number at least two. IsCPTP is the existing completely positive trace-preserving predicate on complex-linear maps of d by d matrices. For every natural dimension d and every d by d complex matrix U, conjugation by U is LinearMap.mulRight ℂ (star U) after LinearMap.mulLeft ℂ U, equal to LinearMap.mulLeftRight ℂ (U, star U). The displayed claim uses unitaryChannel in both targets. The two targets are conjugation by star U and by Matrix.transpose U. The quantifier ranges over every randomisation-consistent bijection of this channel set.

**Theorem 1.4 (Pauli spectral projectors are positive semidefinite).**

$$\forall a \in \operatorname{Fin}\left(3\right),\; \forall e \in Bool,\; \operatorname{Matrix}.\operatorname{PosSemidef}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Magic}.\operatorname{WignerDistanceMinimum}.\operatorname{spectral}\left([\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Information}.\operatorname{StabilizerPairLocalUnitaryInequivalence}.\operatorname{Pauli}.\operatorname{X}, \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Information}.\operatorname{StabilizerPairLocalUnitaryInequivalence}.\operatorname{Pauli}.\operatorname{Y}, \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Information}.\operatorname{StabilizerPairLocalUnitaryInequivalence}.\operatorname{Pauli}.\operatorname{Z}]\left(a\right), \operatorname{if}\left(\right) e = true \operatorname{then}\left(\right) 1 \operatorname{else}\left(\right) 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/ChannelTimeReversalNoGo.density_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every axis index a in Fin 3 and Boolean sign e, the spectral projector of the Pauli axis a with sign e is positive semidefinite.

**Theorem 1.5 (Pauli spectral projectors have trace one).**

$$\forall a \in \operatorname{Fin}\left(3\right),\; \forall e \in Bool,\; \operatorname{Matrix}.\operatorname{trace}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Magic}.\operatorname{WignerDistanceMinimum}.\operatorname{spectral}\left([\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Information}.\operatorname{StabilizerPairLocalUnitaryInequivalence}.\operatorname{Pauli}.\operatorname{X}, \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Information}.\operatorname{StabilizerPairLocalUnitaryInequivalence}.\operatorname{Pauli}.\operatorname{Y}, \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Information}.\operatorname{StabilizerPairLocalUnitaryInequivalence}.\operatorname{Pauli}.\operatorname{Z}]\left(a\right), \operatorname{if}\left(\right) e = true \operatorname{then}\left(\right) 1 \operatorname{else}\left(\right) 0\right)\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/ChannelTimeReversalNoGo.density_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every axis index a in Fin 3 and Boolean sign e, the spectral projector of the Pauli axis a with sign e has trace one.

**Theorem 1.6 (Time-reversal symmetries do not exist).**

$$\forall d \in \mathbb{N},\; (2 \le d) \Rightarrow (\forall S \in \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right) \to \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{IsChannelSymmetry}\left(S\right)) \Rightarrow ((\neg (\forall U \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (U \in \operatorname{Matrix}.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)) \Rightarrow (S\left(\operatorname{unitaryChannel}\left(U\right)\right) = \operatorname{unitaryChannel}\left(\operatorname{star}\left(U\right)\right)))) \land (\neg (\forall U \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (U \in \operatorname{Matrix}.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)) \Rightarrow (S\left(\operatorname{unitaryChannel}\left(U\right)\right) = \operatorname{unitaryChannel}\left(\operatorname{Matrix}.\operatorname{transpose}\left(U\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/ChannelTimeReversalNoGo.result` (`✓ std3`). ∎

*Resolves.* `Problems/chiribella-aurell-zyczkowski-2021-channel-time-reversal` (proved) by `D5/S3/QuantumChannels/ChannelTimeReversalNoGo.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"chiribella-aurell-zyczkowski-2021-channel-time-reversal","declaration_gid":"D5/S3/QuantumChannels/ChannelTimeReversalNoGo.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Giulio Chiribella and Erik Aurell and Karol Życzkowski (2021). *Symmetries of quantum evolutions*. DOI: [10.1103/PhysRevResearch.3.033028](https://doi.org/10.1103/PhysRevResearch.3.033028). URL: <https://arxiv.org/abs/2101.04962>.

*Commentary.*

For dimensions at least three, Bi_basic forces three finite-block identities; diagonal_contradiction makes the positive block have trace zero, contradicting its trace one. For qubits, finite_pauli_identity and unital_reversed identify the action on unital channels. The pure_preimage and pure_density_rotation lemmas supply a unitary rotation of a pure replacement preimage. The forced_witness_output identity then gives diag(9/8, -1/8), whose negative diagonal entry proves inverse_unitary_no_go. Double transposition preserves complete positivity, trace preservation and convex mixtures, is involutive, and sends conjugation by the transpose of U to conjugation by star U. Composing with this transformation reduces the transpose target to the adjoint target.

## References

- Truth anchor: `D5/S3/QuantumChannels/ChannelTimeReversalNoGo.IsChannelSymmetry`
- Truth anchor: `D5/S3/QuantumChannels/ChannelTimeReversalNoGo.claim`
- Truth anchor: `D5/S3/QuantumChannels/ChannelTimeReversalNoGo.density_psd`
- Truth anchor: `D5/S3/QuantumChannels/ChannelTimeReversalNoGo.density_trace`
- Truth anchor: `D5/S3/QuantumChannels/ChannelTimeReversalNoGo.result`
- Truth anchor: `D5/S3/QuantumChannels/ChannelTimeReversalNoGo.unitaryChannel`
- Dependency: [D5/S3/Quantum/Entanglement/ElegantJointMeasurementSourceNoise](../Quantum/Entanglement/ElegantJointMeasurementSourceNoise.md)
- Dependency: [D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds](../Quantum/Entanglement/GraphDensity/FormationBounds.md)
- Dependency: [D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction](../Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.md)
- Dependency: [D5/S3/Quantum/Fibers/RankOneFeedbackProtocol](../Quantum/Fibers/RankOneFeedbackProtocol.md)
- Dependency: [D5/S3/Quantum/Information/RenyiInformationCombiningOrderThree](../Quantum/Information/RenyiInformationCombiningOrderThree.md)
- Dependency: [D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation](../Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence](../Quantum/QuantumChannels/IptPptSquaredEquivalence.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation](../Quantum/QuantumChannels/PositiveFilterTransposeRefutation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum](../Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation](../Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.md)
- Dependency: [D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl](../Quantum/RandomCircuits/HaarTwoCopyTwirl.md)
- Dependency: [D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness](PauliThreeWeightBayesianInverseUniqueness.md)
