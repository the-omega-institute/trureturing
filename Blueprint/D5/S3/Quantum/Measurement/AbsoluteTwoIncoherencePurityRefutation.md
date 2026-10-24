# AbsoluteTwoIncoherencePurityRefutation

## Abstract

Absolute two-incoherence beyond the purity bound.

**Definition 1.1 (IsAbsolutelyKIncoherent).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{k} : \mathbb{N}) , \forall (\operatorname{rho} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \mathbb{C}) , \operatorname{IsAbsolutelyKIncoherent} \operatorname{k} \operatorname{rho} = ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Information}.\operatorname{SLDSpectralEnergy}.\operatorname{IsDensity} \operatorname{rho}) \land (\forall (\operatorname{U} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \mathbb{C}) , (\operatorname{U} \in \operatorname{Matrix}.\operatorname{unitaryGroup} (\operatorname{Fin} \operatorname{n}) \mathbb{C}) \to \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Measurement}.\operatorname{FactorWidthTwoCone}.\operatorname{IsKIncoherentSum} \operatorname{k} (\operatorname{U} \cdot \operatorname{rho} \cdot \operatorname{star} (\operatorname{U}))))$$

*Formalization.* `D5/S3/Quantum/Measurement/AbsoluteTwoIncoherencePurityRefutation.IsAbsolutelyKIncoherent` (`✓ std3`).

*Citation.* Nathaniel Johnston; Shirin Moein; Rajesh Pereira; Sarah Plosker (2022). *Absolutely k-incoherent quantum states and spectral inequalities for factor width of a matrix*. DOI: [10.1103/PhysRevA.106.052417](https://doi.org/10.1103/PhysRevA.106.052417). URL: <https://arxiv.org/abs/2205.05110v2>.

*Commentary.*

Definition 3, page 10: “A mixed quantum state ρ ∈ Mₙ⁺ is absolutely k-incoherent if UρU* ∈ I_{k,n} for all unitary matrices U ∈ Mₙ.” The matrix has positive semidefinite trace-one density, and every unitary conjugate is a finite sum of outer products of k-sparse vectors.

**Definition 1.2 (claim).**

$$\operatorname{claim} = (\forall (\operatorname{n} : \mathbb{N}) , (4 \leq \operatorname{n}) \to \forall (\operatorname{rho} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \mathbb{C}) , (\operatorname{IsAbsolutelyKIncoherent} 2 \operatorname{rho}) \to (((\operatorname{rho} \cdot \operatorname{rho})).\operatorname{trace}).\operatorname{re} \leq \frac{1}{((\operatorname{n} : \mathbb{R}) - 1)})$$

*Formalization.* `D5/S3/Quantum/Measurement/AbsoluteTwoIncoherencePurityRefutation.claim` (`✓ std3`).

*Citation.* Nathaniel Johnston; Shirin Moein; Rajesh Pereira; Sarah Plosker (2022). *Absolutely k-incoherent quantum states and spectral inequalities for factor width of a matrix*. DOI: [10.1103/PhysRevA.106.052417](https://doi.org/10.1103/PhysRevA.106.052417). URL: <https://arxiv.org/abs/2205.05110v2>.

*Commentary.*

Section 5, page 17: “Theorem 7 gives a sufficient condition for absolute 2-incoherence that is also necessary in dimension n = 3. It is unclear whether or not it is necessary in dimension n = 4 or higher.” The natural number n ranges over dimensions at least four; purity is the real trace of the square.

**Theorem 1.3 (result).**

$$\neg (\forall (\operatorname{n} : \mathbb{N}) , (4 \leq \operatorname{n}) \to \forall (\operatorname{rho} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \mathbb{C}) , (\operatorname{IsAbsolutelyKIncoherent} 2 \operatorname{rho}) \to (((\operatorname{rho} \cdot \operatorname{rho})).\operatorname{trace}).\operatorname{re} \leq \frac{1}{((\operatorname{n} : \mathbb{R}) - 1)})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/AbsoluteTwoIncoherencePurityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/jmpp-2022-absolute-two-incoherence-purity` (refuted) by `D5/S3/Quantum/Measurement/AbsoluteTwoIncoherencePurityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"jmpp-2022-absolute-two-incoherence-purity","declaration_gid":"D5/S3/Quantum/Measurement/AbsoluteTwoIncoherencePurityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston; Shirin Moein; Rajesh Pereira; Sarah Plosker (2022). *Absolutely k-incoherent quantum states and spectral inequalities for factor width of a matrix*. DOI: [10.1103/PhysRevA.106.052417](https://doi.org/10.1103/PhysRevA.106.052417). URL: <https://arxiv.org/abs/2205.05110v2>.

*Commentary.*

A density matrix in dimension five is absolutely two-incoherent and has purity strictly greater than one quarter. The rank of a squared-modulus Gram matrix is at most four, which separates the relevant unitary orbit from the trace-one locally positive matrices.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/AbsoluteTwoIncoherencePurityRefutation.IsAbsolutelyKIncoherent`
- Truth anchor: `D5/S3/Quantum/Measurement/AbsoluteTwoIncoherencePurityRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/AbsoluteTwoIncoherencePurityRefutation.result`
- Dependency: [D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics](../Decoherence/ProjectedUnistochasticDynamics.md)
- Dependency: [D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound](../Entanglement/GHZMeasureBiseparableBound.md)
- Dependency: [D5/S3/Quantum/Information/SLDSpectralEnergy](../Information/SLDSpectralEnergy.md)
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../Matrix/CartesianVariance.md)
- Dependency: [D5/S3/Quantum/Matrix/CommutatorGap](../Matrix/CommutatorGap.md)
- Dependency: [D5/S3/Quantum/Measurement/AntidistinguishabilityOverlapNonTight](AntidistinguishabilityOverlapNonTight.md)
- Dependency: [D5/S3/Quantum/Measurement/FactorWidthTwoCone](FactorWidthTwoCone.md)
- Dependency: [D5/S3/Quantum/Measurement/OverlapLowRankDistance](OverlapLowRankDistance.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound](../TensorNetworks/BridgeGraph/QuantumMaxFlowBound.md)
