# Lidar Restricted Anticoncentration Refutation

## Abstract

LidarRestrictedAnticoncentrationRefutation describes the forced-twin mechanism for QPU-restricted IQP circuits.

**Theorem 1.1 (joint fractional bound).**

$$\forall (\operatorname{m} : \mathbb{N}), (((\operatorname{F4} \operatorname{m}).\operatorname{Nonempty}) \to (\forall (\operatorname{Z} : \operatorname{Finset} ((\operatorname{Fin} (6 \cdot \operatorname{m}) \times \operatorname{Fin} (6 \cdot \operatorname{m}))) \times ((\operatorname{Fin} (6 \cdot \operatorname{m})) \to \mathbb{R}) \to \mathbb{R}), ((\operatorname{Integrable} (\operatorname{fun} \operatorname{w} \mapsto \operatorname{Real}.\operatorname{sqrt} (\operatorname{Z} \operatorname{w})) (\operatorname{joint} \operatorname{m})) \to ((\forall \operatorname{G} \in \operatorname{F4} \operatorname{m}, (\int \theta, \operatorname{Real}.\operatorname{sqrt} (\operatorname{Z} (\operatorname{G},\theta)) d\operatorname{uniformAngles} \operatorname{m}) \leq (47 / 48 : \mathbb{R})^{\operatorname{m}}) \to ((\int \operatorname{w}, \operatorname{Real}.\operatorname{sqrt} (\operatorname{Z} \operatorname{w}) d\operatorname{joint} \operatorname{m}) \leq (47 / 48 : \mathbb{R})^{\operatorname{m}})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.joint_fractional_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated joint fractional bound relation for the finite twin-pair calculation.

**Theorem 1.2 (factor nonempty).**

$$\forall (\operatorname{m} : \mathbb{N}), ([\operatorname{NeZero} \operatorname{m}] \to ((1 < \operatorname{m}) \to ((\operatorname{F4} \operatorname{m}).\operatorname{Nonempty})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.factor_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A four-factor exists: the connector-free factor uses the four internal neighbours of every vertex. The probability law on factors is therefore normalized.

**Theorem 1.3 (literal joint probability).**

$$\forall (\operatorname{m} : \mathbb{N}), ([\operatorname{NeZero} \operatorname{m}] \to ((1 < \operatorname{m}) \to (\operatorname{MeasureTheory}.\operatorname{IsProbabilityMeasure} (\operatorname{joint} \operatorname{m}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.literal_joint_probability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated literal joint probability relation for the finite twin-pair calculation.

**Definition 1.4 (claim).**

$$\operatorname{claim} \iff \neg \exists \operatorname{a} \operatorname{b} : \mathbb{R}, 0 < \operatorname{a} \land 0 < \operatorname{b} \land \forall \operatorname{m} : \mathbb{N}, 3 \leq \operatorname{m} \to \forall \operatorname{s} : (\operatorname{Fin} (6 \cdot \operatorname{m}) \to \operatorname{Bool}), \operatorname{b} \leq \operatorname{tailProbability} \operatorname{m} \operatorname{a} \operatorname{s}$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.claim` (`✓ std3`).

*Citation.* D. A. Lidar (2025). *Digital-Analog-Digital Quantum Supremacy*. DOI: [10.48550/arXiv.2512.07127](https://doi.org/10.48550/arXiv.2512.07127). URL: <https://arxiv.org/abs/2512.07127v1>.

*Commentary.*

D. A. Lidar, Digital-Analog-Digital Quantum Supremacy, arXiv:2512.07127v1, p. 4, Conjecture 2, verbatim: Let \{\mH_n\} be a family of hardware graphs as in \cref{def:QPU-R-E}. For each n, draw \mG\sim \mathrm{Unif}[\mF_d(\mH_n)] and \theta\sim \mathrm{Unif}[0,2\pi)^n. For any fixed choice of single-qubit angles \{v_i\} in \cref{eq:HZ'}, there exist constants a,b>0 (depending only on d) such that for every s\in\{0,1\}^n, \Pr_{\mG,\theta} \bigl[ P_{\UIQP^{(\theta)}}(s)\ge a 2^{-n} \bigr] \ge b. The definition claim is the NEGATION of this conclusion for the displayed hardware family, d=4, fixed angles pi/7 and n=6m, m>=3. A universal conclusion for every hardware family must hold on this subsequence. The hardware is simple and five-regular, and F4 is nonempty. Thus a theorem of claim refutes the universal source statement. Formulas retain Lean application and binder notation; a centered dot in a constant lambda denotes an anonymous unused binder. Casts display their target types, and products and integrals bind their displayed variables.

**Theorem 1.5 (result).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/lidar-2025-qpu-restricted-anticoncentration-refutation` (refuted) by `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lidar-2025-qpu-restricted-anticoncentration-refutation","declaration_gid":"D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* D. A. Lidar (2025). *Digital-Analog-Digital Quantum Supremacy*. DOI: [10.48550/arXiv.2512.07127](https://doi.org/10.48550/arXiv.2512.07127). URL: <https://arxiv.org/abs/2512.07127v1>.

*Commentary.*

No fixed positive a and b work for the cyclic six-vertex-component family. The forced twin pairs yield a product marginal, and the uniform square-root moment contracts by 47/48 per component. Markov bounds each output tail by inverse sqrt(a) times (47/48)^m. This tends to zero and contradicts a positive uniform lower bound. Conjecture 1 is untouched; the source Theorem 2 remains a conditional statement whose general anticoncentration hypothesis is refuted.

**Theorem 1.6 (circuit amplitude literal).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{G} : \operatorname{Finset} ((\operatorname{Fin} (6 \cdot \operatorname{m}) \times \operatorname{Fin} (6 \cdot \operatorname{m})))), (\forall (\theta : (\operatorname{Fin} (6 \cdot \operatorname{m})) \to \mathbb{R}), (\forall (\operatorname{s} : (\operatorname{Fin} (6 \cdot \operatorname{m}) \to \operatorname{Bool})), (\operatorname{circuit} \operatorname{G} \theta \operatorname{s} (\operatorname{fun} \cdot \mapsto \operatorname{false}) = \sum \operatorname{z} : (\operatorname{Fin} (6 \cdot \operatorname{m}) \to \operatorname{Bool}), (\operatorname{tensorOp} (\operatorname{fun} \cdot : \operatorname{Fin} (6 \cdot \operatorname{m}) \mapsto \operatorname{hadamard}) (\operatorname{fun} \operatorname{i} \mapsto \operatorname{if} \operatorname{s} \operatorname{i} \operatorname{then} 1 \operatorname{else} 0) (\operatorname{fun} \operatorname{i} \mapsto \operatorname{if} \operatorname{z} \operatorname{i} \operatorname{then} 1 \operatorname{else} 0)) \cdot \operatorname{Complex}.\operatorname{exp} (-\operatorname{Complex}.\operatorname{I} \cdot ((\operatorname{HZ} \operatorname{G} \operatorname{z} + \sum \operatorname{i}, \theta \operatorname{i} \cdot \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumBounds}.\operatorname{MerminMeasurementDependence}.\operatorname{boolSign} (\operatorname{z} \operatorname{i}) / 2 : \mathbb{R}) : \mathbb{C})) \cdot (\operatorname{tensorOp} (\operatorname{fun} \cdot : \operatorname{Fin} (6 \cdot \operatorname{m}) \mapsto \operatorname{hadamard}) (\operatorname{fun} \operatorname{i} \mapsto \operatorname{if} \operatorname{z} \operatorname{i} \operatorname{then} 1 \operatorname{else} 0) (\operatorname{fun} \operatorname{i} \mapsto \operatorname{if} (\operatorname{fun} \cdot \mapsto \operatorname{false}) \operatorname{i} \operatorname{then} 1 \operatorname{else} 0))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.circuit_amplitude_literal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated circuit amplitude literal relation for the finite twin-pair calculation.

**Definition 1.7 (graphAmplitude).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{G} : \operatorname{Finset} ((\operatorname{Fin} (6 \cdot \operatorname{m}) \times \operatorname{Fin} (6 \cdot \operatorname{m})))), (\forall (\operatorname{z} : (\operatorname{Fin} (6 \cdot \operatorname{m}) \to \operatorname{Bool})), (\operatorname{graphAmplitude} \operatorname{G} \operatorname{z} = (\operatorname{tensorOp} (\operatorname{fun} \cdot : \operatorname{Fin} (6 \cdot \operatorname{m}) \mapsto \operatorname{hadamard}) (\operatorname{fun} \operatorname{i} \mapsto \operatorname{if} \operatorname{z} \operatorname{i} \operatorname{then} 1 \operatorname{else} 0) (\operatorname{fun} \operatorname{i} \mapsto \operatorname{if} (\operatorname{fun} \cdot \mapsto \operatorname{false}) \operatorname{i} \operatorname{then} 1 \operatorname{else} 0)) \cdot \prod \operatorname{e} \in \operatorname{G}, (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{RandomizedGraphNegativityRefutation}.\operatorname{czPhase} (\operatorname{s} ((0 : (\operatorname{Fin} 2)), 1)) (\operatorname{fun} \operatorname{czIndex} \mapsto \operatorname{if} \operatorname{czIndex} = 0 \operatorname{then} (\operatorname{z} \operatorname{e}.1) \operatorname{else} (\operatorname{z} \operatorname{e}.2))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.graphAmplitude` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines graphAmplitude. Ordered edge pairs retain both orientations off the hardware-factor domain, whereas graphState identifies them.

**Definition 1.8 (measurementRow).**

$$\forall (\operatorname{m} : \mathbb{N}), \forall (\operatorname{s} : ((\operatorname{Fin} (6\cdot\operatorname{m})) \to \operatorname{Bool})), \forall (\varphi : ((\operatorname{Fin} (6\cdot\operatorname{m})) \to \mathbb{R})), \operatorname{measurementRow} \operatorname{s} \varphi = (((\operatorname{tensorOp} (\operatorname{fun} \operatorname{i} \mapsto (\operatorname{hadamard} \cdot \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{PrecessionSpinOneSeparableBound}.\operatorname{rotation} 1 ((\varphi \operatorname{i}))))) (\operatorname{fun} \operatorname{i} \mapsto (\operatorname{if} ((\operatorname{s} \operatorname{i})) \operatorname{then} 1 \operatorname{else} 0))) \circ (\operatorname{fun} \operatorname{z} \operatorname{i} \mapsto (\operatorname{if} ((\operatorname{z} \operatorname{i})) \operatorname{then} 1 \operatorname{else} 0)))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.measurementRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines measurementRow.

**Theorem 1.9 (factor output graph probability).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{G} : \operatorname{Finset} ((\operatorname{Fin} (6 \cdot \operatorname{m}) \times \operatorname{Fin} (6 \cdot \operatorname{m})))), ((\operatorname{G} \in \operatorname{F4} \operatorname{m}) \to (\forall (\theta : (\operatorname{Fin} (6 \cdot \operatorname{m})) \to \mathbb{R}), (\forall (\operatorname{s} : (\operatorname{Fin} (6 \cdot \operatorname{m}) \to \operatorname{Bool})), (\operatorname{outputProbability} \operatorname{G} \theta \operatorname{s} = \operatorname{Complex}.\operatorname{normSq} (\sum \operatorname{z} : (\operatorname{Fin} (6 \cdot \operatorname{m}) \to \operatorname{Bool}), \operatorname{graphAmplitude} \operatorname{G} \operatorname{z} \cdot \operatorname{measurementRow} \operatorname{s} (\operatorname{fun} \operatorname{i} \mapsto \theta \operatorname{i} + 2 \cdot (\operatorname{Real}.\operatorname{pi} / 7)) \operatorname{z}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.factor_output_graph_probability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated factor output graph probability relation for the finite twin-pair calculation.

**Theorem 1.10 (W false squared).**

$$((\operatorname{hadamard} (\operatorname{if} \operatorname{false} \operatorname{then} 1 \operatorname{else} 0) (\operatorname{if} \operatorname{false} \operatorname{then} 1 \operatorname{else} 0)))^{2} = (1 / 2 : \mathbb{C})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.W_false_squared` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated W false squared relation for the finite twin-pair calculation.

**Theorem 1.11 (one qubit effect zero).**

$$\forall (\alpha : \mathbb{R}), (\forall (\operatorname{r} : \operatorname{Bool}), (\forall (\operatorname{r}' : \operatorname{Bool}), (((\operatorname{hadamard} (\operatorname{if} \operatorname{false} \operatorname{then} 1 \operatorname{else} 0) (\operatorname{if} \operatorname{r} \operatorname{then} 1 \operatorname{else} 0)) \cdot \operatorname{Complex}.\operatorname{exp} (-\operatorname{Complex}.\operatorname{I} \cdot ((\alpha \cdot \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumBounds}.\operatorname{MerminMeasurementDependence}.\operatorname{boolSign} \operatorname{r} / 2 : \mathbb{R}) : \mathbb{C}))) \cdot \operatorname{star} ((\operatorname{hadamard} (\operatorname{if} \operatorname{false} \operatorname{then} 1 \operatorname{else} 0) (\operatorname{if} \operatorname{r}' \operatorname{then} 1 \operatorname{else} 0)) \cdot \operatorname{Complex}.\operatorname{exp} (-\operatorname{Complex}.\operatorname{I} \cdot ((\alpha \cdot \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumBounds}.\operatorname{MerminMeasurementDependence}.\operatorname{boolSign} \operatorname{r}' / 2 : \mathbb{R}) : \mathbb{C}))) = \operatorname{effect} \alpha \operatorname{r}' \operatorname{r})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.one_qubit_effect_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated one qubit effect zero relation for the finite twin-pair calculation.

**Theorem 1.12 (graph probability effect zero).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{G} : \operatorname{Finset} ((\operatorname{Fin} (6 \cdot \operatorname{m}) \times \operatorname{Fin} (6 \cdot \operatorname{m})))), (\forall (\varphi : (\operatorname{Fin} (6 \cdot \operatorname{m})) \to \mathbb{R}), ((\operatorname{Complex}.\operatorname{normSq} (\sum \operatorname{z} : (\operatorname{Fin} (6 \cdot \operatorname{m}) \to \operatorname{Bool}), \operatorname{graphAmplitude} \operatorname{G} \operatorname{z} \cdot \operatorname{measurementRow} (\operatorname{fun} \cdot \mapsto \operatorname{false}) \varphi \operatorname{z}) : \mathbb{C}) = \sum \operatorname{z} : (\operatorname{Fin} (6 \cdot \operatorname{m}) \to \operatorname{Bool}), \sum \operatorname{z}' : (\operatorname{Fin} (6 \cdot \operatorname{m}) \to \operatorname{Bool}), \operatorname{graphAmplitude} \operatorname{G} \operatorname{z} \cdot \operatorname{star} (\operatorname{graphAmplitude} \operatorname{G} \operatorname{z}') \cdot \prod \operatorname{i}, \operatorname{effect} (\varphi \operatorname{i}) (\operatorname{z}' \operatorname{i}) (\operatorname{z} \operatorname{i}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.graph_probability_effect_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated graph probability effect zero relation for the finite twin-pair calculation.

**Definition 1.13 (densityProbability).**

$$\forall (\operatorname{A} : \operatorname{Type}), [\operatorname{Fintype} \operatorname{A}] \to \forall (\operatorname{k} : \mathbb{N}), \forall (\rho : (\operatorname{Matrix} (\operatorname{A} \times ((\operatorname{Fin} \operatorname{k}) \to \operatorname{Bool})) (\operatorname{A} \times ((\operatorname{Fin} \operatorname{k}) \to \operatorname{Bool})) \mathbb{C})), \forall (\operatorname{E} : (\operatorname{A} \to (\operatorname{A} \to \mathbb{C}))), \forall (\alpha : ((\operatorname{Fin} \operatorname{k}) \to \mathbb{R})), \operatorname{densityProbability} \operatorname{k} \rho \operatorname{E} \alpha = (\operatorname{Matrix}.\operatorname{trace} (\rho \cdot (\operatorname{Matrix}.\operatorname{kronecker} ((\operatorname{Matrix}.\operatorname{of} \operatorname{E}).\operatorname{transpose}) ((\operatorname{tensorOp} (\operatorname{fun} \operatorname{i} \mapsto (\operatorname{Matrix}.\operatorname{vecMulVec} (\operatorname{fun} (\operatorname{r} : (\operatorname{Fin} 2)) \mapsto (\operatorname{star} ((\operatorname{hadamard} \cdot \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{PrecessionSpinOneSeparableBound}.\operatorname{rotation} 1 ((\alpha \operatorname{i}))) 0 \operatorname{r}))) (\operatorname{star} (\operatorname{fun} (\operatorname{r} : (\operatorname{Fin} 2)) \mapsto (\operatorname{star} ((\operatorname{hadamard} \cdot \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{PrecessionSpinOneSeparableBound}.\operatorname{rotation} 1 ((\alpha \operatorname{i}))) 0 \operatorname{r}))))))).\operatorname{submatrix} (\operatorname{fun} (\operatorname{z} : ((\operatorname{Fin} \operatorname{k}) \to \operatorname{Bool})) \mapsto (\operatorname{fun} \operatorname{i} \mapsto (\operatorname{if} ((\operatorname{z} \operatorname{i})) \operatorname{then} 1 \operatorname{else} 0))) (\operatorname{fun} (\operatorname{z} : ((\operatorname{Fin} \operatorname{k}) \to \operatorname{Bool})) \mapsto (\operatorname{fun} \operatorname{i} \mapsto (\operatorname{if} ((\operatorname{z} \operatorname{i})) \operatorname{then} 1 \operatorname{else} 0)))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.densityProbability` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines densityProbability.

**Definition 1.14 (complementEquiv).**

$$\forall (\operatorname{m} : \mathbb{N}), (\operatorname{complementEquiv} \operatorname{m} = ((\operatorname{finProdFinEquiv}.\operatorname{trans} (\operatorname{finCongr} (\operatorname{Nat}.\operatorname{mul}_{\operatorname{comm}} \operatorname{m} 4))).\operatorname{symm}.\operatorname{arrowCongr} (\operatorname{Equiv}.\operatorname{refl} \operatorname{Bool})).\operatorname{trans} (\operatorname{Equiv}.\operatorname{curry} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} 4) \operatorname{Bool}))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.complementEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines complementEquiv.

**Definition 1.15 (reindexedTwinAmplitude).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{qC} : (\operatorname{Fin} \operatorname{m} \to \operatorname{Fin} 4 \to \operatorname{Bool}) \to \operatorname{Bool}), (\forall (\operatorname{xz} : (\operatorname{Fin} \operatorname{m} \to \operatorname{Bool} \times \operatorname{Bool}) \times (\operatorname{Fin} (4\cdot\operatorname{m}) \to \operatorname{Bool})), (\operatorname{reindexedTwinAmplitude} \operatorname{m} \operatorname{qC} \operatorname{xz} = \operatorname{twinAmplitude} \operatorname{m} \operatorname{qC} (\operatorname{xz}.1, \operatorname{complementEquiv} \operatorname{m} \operatorname{xz}.2))))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.reindexedTwinAmplitude` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines reindexedTwinAmplitude.

**Theorem 1.16 (reindexed twin marginal).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{qC} : (\operatorname{Fin} \operatorname{m} \to \operatorname{Fin} 4 \to \operatorname{Bool}) \to \operatorname{Bool}), (\forall (\operatorname{x} : \operatorname{Fin} \operatorname{m} \to \operatorname{Bool} \times \operatorname{Bool}), (\forall (\operatorname{x}' : \operatorname{Fin} \operatorname{m} \to \operatorname{Bool} \times \operatorname{Bool}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Information}.\operatorname{PartialTraceMutualInformation}.\operatorname{partialTraceRight} (\operatorname{Matrix}.\operatorname{vecMulVec} (\operatorname{reindexedTwinAmplitude} \operatorname{m} \operatorname{qC}) (\operatorname{star} (\operatorname{reindexedTwinAmplitude} \operatorname{m} \operatorname{qC}))) \operatorname{x} \operatorname{x}' = \prod \operatorname{i}, \operatorname{pairDensity} (\operatorname{x} \operatorname{i}) (\operatorname{x}' \operatorname{i})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.reindexed_twin_marginal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated reindexed twin marginal relation for the finite twin-pair calculation.

**Definition 1.17 (retainedEffect).**

$$\forall (\operatorname{m} : \mathbb{N}), \forall (\varphi : (\operatorname{Fin} \operatorname{m} \to (\mathbb{R} \times \mathbb{R}))), \forall (\operatorname{x} : (\operatorname{Fin} \operatorname{m} \to (\operatorname{Bool} \times \operatorname{Bool}))), \forall (\operatorname{x}' : (\operatorname{Fin} \operatorname{m} \to (\operatorname{Bool} \times \operatorname{Bool}))), \operatorname{retainedEffect} \operatorname{m} \varphi \operatorname{x} \operatorname{x}' = (\operatorname{Matrix}.\operatorname{vecMulVec} (\operatorname{retainedRow} \operatorname{m} \varphi) (\operatorname{star} (\operatorname{retainedRow} \operatorname{m} \varphi))) \operatorname{x} \operatorname{x}'$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.retainedEffect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines retainedEffect.

**Definition 1.18 (twinDensityProbability).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{qC} : (\operatorname{Fin} \operatorname{m} \to \operatorname{Fin} 4 \to \operatorname{Bool}) \to \operatorname{Bool}), (\forall (\varphi : \operatorname{Fin} \operatorname{m} \to \mathbb{R} \times \mathbb{R}), (\forall (\alpha : \operatorname{Fin} (4\cdot\operatorname{m}) \to \mathbb{R}), (\operatorname{twinDensityProbability} \operatorname{m} \operatorname{qC} \varphi \alpha = \operatorname{densityProbability} (4\cdot\operatorname{m}) (\operatorname{Matrix}.\operatorname{vecMulVec} (\operatorname{reindexedTwinAmplitude} \operatorname{m} \operatorname{qC}) (\operatorname{star} (\operatorname{reindexedTwinAmplitude} \operatorname{m} \operatorname{qC}))) (\operatorname{retainedEffect} \operatorname{m} \varphi) \alpha))))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.twinDensityProbability` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines twinDensityProbability.

**Definition 1.19 (normalizedTwinDensity).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{qC} : (\operatorname{Fin} \operatorname{m} \to \operatorname{Fin} 4 \to \operatorname{Bool}) \to \operatorname{Bool}), (\forall (\varphi : \operatorname{Fin} \operatorname{m} \to \mathbb{R} \times \mathbb{R}), (\forall (\alpha : \operatorname{Fin} (4\cdot\operatorname{m}) \to \mathbb{R}), (\operatorname{normalizedTwinDensity} \operatorname{m} \operatorname{qC} \varphi \alpha = (2 : \mathbb{R})^{6\cdot\operatorname{m}} \cdot (\operatorname{twinDensityProbability} \operatorname{m} \operatorname{qC} \varphi \alpha).\operatorname{re}))))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.normalizedTwinDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines normalizedTwinDensity.

**Theorem 1.20 (normalized twin conditional mean).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{qC} : (\operatorname{Fin} \operatorname{m} \to \operatorname{Fin} 4 \to \operatorname{Bool}) \to \operatorname{Bool}), (\forall (\varphi : \operatorname{Fin} \operatorname{m} \to \mathbb{R} \times \mathbb{R}), ((\int \alpha, \operatorname{normalizedTwinDensity} \operatorname{m} \operatorname{qC} \varphi \alpha d\operatorname{Measure}.\operatorname{pi} (\operatorname{fun} \cdot \mapsto (\operatorname{ProbabilityTheory}.\operatorname{cond} \operatorname{volume} (\operatorname{Set}.\operatorname{Ico} 0 (2 \cdot \operatorname{Real}.\operatorname{pi}))))) = \prod \operatorname{i}, (1 + \operatorname{Real}.\operatorname{cos} (\varphi \operatorname{i}).1 \cdot \operatorname{Real}.\operatorname{cos} (\varphi \operatorname{i}).2))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.normalized_twin_conditional_mean` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated normalized twin conditional mean relation for the finite twin-pair calculation.

**Definition 1.21 (retainedRow).**

$$\forall (\operatorname{m} : \mathbb{N}), \forall (\varphi : ((\operatorname{Fin} \operatorname{m}) \to (\mathbb{R} \times \mathbb{R}))), \forall (\operatorname{x} : ((\operatorname{Fin} \operatorname{m}) \to (\operatorname{Bool} \times \operatorname{Bool}))), \operatorname{retainedRow} \operatorname{m} \varphi \operatorname{x} = ((\operatorname{tensorOp} (\operatorname{fun} (\operatorname{i} : (\operatorname{Fin} (\operatorname{m} + \operatorname{m}))) \mapsto (\operatorname{Sum}.\operatorname{elim} (\operatorname{fun} \operatorname{j} \mapsto (\operatorname{hadamard} \cdot \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{PrecessionSpinOneSeparableBound}.\operatorname{rotation} 1 ((\varphi \operatorname{j}).1))) (\operatorname{fun} \operatorname{j} \mapsto (\operatorname{hadamard} \cdot \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{PrecessionSpinOneSeparableBound}.\operatorname{rotation} 1 ((\varphi \operatorname{j}).2))) (\operatorname{finSumFinEquiv}.\operatorname{symm} \operatorname{i})))) (\operatorname{fun} \cdot \mapsto 0) (\operatorname{fun} \operatorname{i} \mapsto (\operatorname{if} ((\operatorname{Sum}.\operatorname{elim} (\operatorname{fun} \operatorname{j} \mapsto (\operatorname{x} \operatorname{j}).1) (\operatorname{fun} \operatorname{j} \mapsto (\operatorname{x} \operatorname{j}).2) (\operatorname{finSumFinEquiv}.\operatorname{symm} \operatorname{i}))) \operatorname{then} 1 \operatorname{else} 0)))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.retainedRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines retainedRow.

**Definition 1.22 (twinProbability).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{qC} : (\operatorname{Fin} \operatorname{m} \to \operatorname{Fin} 4 \to \operatorname{Bool}) \to \operatorname{Bool}), (\forall (\varphi : \operatorname{Fin} \operatorname{m} \to \mathbb{R} \times \mathbb{R}), (\forall (\alpha : \operatorname{Fin} (4\cdot\operatorname{m}) \to \mathbb{R}), (\operatorname{twinProbability} \operatorname{m} \operatorname{qC} \varphi \alpha = \operatorname{Complex}.\operatorname{normSq} (\sum \operatorname{x} : \operatorname{Fin} \operatorname{m} \to \operatorname{Bool} \times \operatorname{Bool}, \sum \operatorname{z} : \operatorname{Fin} (4\cdot\operatorname{m}) \to \operatorname{Bool}, \operatorname{reindexedTwinAmplitude} \operatorname{m} \operatorname{qC} (\operatorname{x},\operatorname{z}) \cdot \operatorname{retainedRow} \operatorname{m} \varphi \operatorname{x} \cdot ((\operatorname{tensorOp} (\operatorname{fun} \operatorname{i} \mapsto (\operatorname{hadamard} \cdot \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{PrecessionSpinOneSeparableBound}.\operatorname{rotation} 1 ((\alpha \operatorname{i}))))) (\operatorname{fun} \cdot \mapsto 0) (\operatorname{fun} \operatorname{i} \mapsto (\operatorname{if} ((\operatorname{z} \operatorname{i})) \operatorname{then} 1 \operatorname{else} 0))))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.twinProbability` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines twinProbability.

**Theorem 1.23 (normSq finite sum).**

$$\forall (\operatorname{I} : \operatorname{Type}), ([\operatorname{Fintype} \operatorname{I}] \to (\forall (\operatorname{f} : \operatorname{I} \to \mathbb{C}), ((\operatorname{Complex}.\operatorname{normSq} (\sum \operatorname{i}, \operatorname{f} \operatorname{i}) : \mathbb{C}) = \sum \operatorname{i}, \sum \operatorname{j}, \operatorname{f} \operatorname{i} \cdot \operatorname{star} (\operatorname{f} \operatorname{j}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.normSq_finite_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated normSq finite sum relation for the finite twin-pair calculation.

**Theorem 1.24 (twin probability density).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{qC} : (\operatorname{Fin} \operatorname{m} \to \operatorname{Fin} 4 \to \operatorname{Bool}) \to \operatorname{Bool}), (\forall (\varphi : \operatorname{Fin} \operatorname{m} \to \mathbb{R} \times \mathbb{R}), (\forall (\alpha : \operatorname{Fin} (4\cdot\operatorname{m}) \to \mathbb{R}), ((\operatorname{twinProbability} \operatorname{m} \operatorname{qC} \varphi \alpha : \mathbb{C}) = \operatorname{twinDensityProbability} \operatorname{m} \operatorname{qC} \varphi \alpha))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.twin_probability_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated twin probability density relation for the finite twin-pair calculation.

**Theorem 1.25 (normalized density nonneg).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{qC} : (\operatorname{Fin} \operatorname{m} \to \operatorname{Fin} 4 \to \operatorname{Bool}) \to \operatorname{Bool}), (\forall (\varphi : \operatorname{Fin} \operatorname{m} \to \mathbb{R} \times \mathbb{R}), (\forall (\alpha : \operatorname{Fin} (4\cdot\operatorname{m}) \to \mathbb{R}), (0 \leq \operatorname{normalizedTwinDensity} \operatorname{m} \operatorname{qC} \varphi \alpha))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.normalized_density_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated normalized density nonneg relation for the finite twin-pair calculation.

**Definition 1.26 (retainedSplit).**

$$\forall (\operatorname{m} : \mathbb{N}), (\operatorname{retainedSplit} \operatorname{m} = (\operatorname{MeasurableEquiv}.\operatorname{sumPiEquivProdPi} (\operatorname{fun} \cdot : \operatorname{Sum} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} \operatorname{m}) \mapsto \mathbb{R})).\operatorname{trans} (\operatorname{MeasurableEquiv}.\operatorname{arrowProdEquivProdArrow} \mathbb{R} \mathbb{R} (\operatorname{Fin} \operatorname{m})).\operatorname{symm})$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.retainedSplit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines retainedSplit. Formulas retain Lean application and binder notation; a centered dot in a constant lambda denotes an anonymous unused binder. Casts display their target types, and products and integrals bind their displayed variables.

**Definition 1.27 (angleSplit).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{e} : (\operatorname{Sum} (\operatorname{Sum} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} \operatorname{m})) (\operatorname{Fin} (4\cdot\operatorname{m}))) \equiv (\operatorname{Fin} (6 \cdot \operatorname{m}))), (\operatorname{angleSplit} \operatorname{m} \operatorname{e} = (\operatorname{MeasurableEquiv}.\operatorname{piCongrLeft} (\operatorname{fun} \cdot : (\operatorname{Sum} (\operatorname{Sum} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} \operatorname{m})) (\operatorname{Fin} (4\cdot\operatorname{m}))) \mapsto \mathbb{R}) \operatorname{e}.\operatorname{symm}).\operatorname{trans} ((\operatorname{MeasurableEquiv}.\operatorname{sumPiEquivProdPi} (\operatorname{fun} \cdot : (\operatorname{Sum} (\operatorname{Sum} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} \operatorname{m})) (\operatorname{Fin} (4\cdot\operatorname{m}))) \mapsto \mathbb{R})).\operatorname{trans} ((\operatorname{retainedSplit} \operatorname{m}).\operatorname{prodCongr} (\operatorname{MeasurableEquiv}.\operatorname{refl} \cdot)))))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.angleSplit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines angleSplit.

**Theorem 1.28 (split integral).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{e} : (\operatorname{Sum} (\operatorname{Sum} (\operatorname{Fin} \operatorname{m}) (\operatorname{Fin} \operatorname{m})) (\operatorname{Fin} (4\cdot\operatorname{m}))) \equiv (\operatorname{Fin} (6 \cdot \operatorname{m}))), (\forall (\operatorname{f} : ((\operatorname{Fin} \operatorname{m} \to \mathbb{R} \times \mathbb{R}) \times (\operatorname{Fin} (4\cdot\operatorname{m}) \to \mathbb{R})) \to \mathbb{R}), ((\int \theta, \operatorname{f} (\operatorname{angleSplit} \operatorname{m} \operatorname{e} \theta) d\operatorname{uniformAngles} \operatorname{m}) = \int \operatorname{w}, \operatorname{f} \operatorname{w} d((\operatorname{Measure}.\operatorname{pi} \operatorname{fun} \cdot : \operatorname{Fin} \operatorname{m} \mapsto \operatorname{pairAngle}).\operatorname{prod} (\operatorname{Measure}.\operatorname{pi} \operatorname{fun} \cdot : \operatorname{Fin} (4\cdot\operatorname{m}) \mapsto (\operatorname{ProbabilityTheory}.\operatorname{cond} \operatorname{volume} (\operatorname{Set}.\operatorname{Ico} 0 (2 \cdot \operatorname{Real}.\operatorname{pi}))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.split_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated split integral relation for the finite twin-pair calculation.

**Theorem 1.29 (gate entry norm le one).**

$$\forall (\alpha : \mathbb{R}), (\forall (\operatorname{b} : \operatorname{Bool}), (\Vert((\operatorname{hadamard} \cdot \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{PrecessionSpinOneSeparableBound}.\operatorname{rotation} 1 (\alpha)) 0 (\operatorname{if} (\operatorname{b}) \operatorname{then} 1 \operatorname{else} 0))\Vert \leq 1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.gate_entry_norm_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated gate entry norm le one relation for the finite twin-pair calculation.

**Theorem 1.30 (normalizedDensity eq).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{qC} : (\operatorname{Fin} \operatorname{m} \to \operatorname{Fin} 4 \to \operatorname{Bool}) \to \operatorname{Bool}), (\forall (\varphi : \operatorname{Fin} \operatorname{m} \to \mathbb{R} \times \mathbb{R}), (\forall (\alpha : \operatorname{Fin} (4\cdot\operatorname{m}) \to \mathbb{R}), (\operatorname{normalizedTwinDensity} \operatorname{m} \operatorname{qC} \varphi \alpha = (2 : \mathbb{R})^{6\cdot\operatorname{m}} \cdot \operatorname{twinProbability} \operatorname{m} \operatorname{qC} \varphi \alpha))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.normalizedDensity_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated normalizedDensity eq relation for the finite twin-pair calculation.

**Theorem 1.31 (twin fractional moment).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{qC} : (\operatorname{Fin} \operatorname{m} \to \operatorname{Fin} 4 \to \operatorname{Bool}) \to \operatorname{Bool}), ((\int \operatorname{w}, \operatorname{Real}.\operatorname{sqrt} (\operatorname{normalizedTwinDensity} \operatorname{m} \operatorname{qC} \operatorname{w}.1 \operatorname{w}.2) d((\operatorname{Measure}.\operatorname{pi} \operatorname{fun} \cdot : \operatorname{Fin} \operatorname{m} \mapsto \operatorname{pairAngle}).\operatorname{prod} (\operatorname{Measure}.\operatorname{pi} \operatorname{fun} \cdot : \operatorname{Fin} (4\cdot\operatorname{m}) \mapsto (\operatorname{ProbabilityTheory}.\operatorname{cond} \operatorname{volume} (\operatorname{Set}.\operatorname{Ico} 0 (2 \cdot \operatorname{Real}.\operatorname{pi})))))) \leq (47 / 48 : \mathbb{R})^{\operatorname{m}}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.twin_fractional_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The conditional mean is the product of 1+cos(alpha)cos(beta). Conditional Cauchy-Schwarz, the polynomial upper bound on sqrt(1+t), and the independent uniform angles yield contraction by at most 47/48 per pair.

**Definition 1.32 (graphProbability).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{G} : \operatorname{Finset} ((\operatorname{Fin} (6 \cdot \operatorname{m}) \times \operatorname{Fin} (6 \cdot \operatorname{m})))), (\forall (\theta : (\operatorname{Fin} (6 \cdot \operatorname{m})) \to \mathbb{R}), (\operatorname{graphProbability} \operatorname{G} \theta = \operatorname{Complex}.\operatorname{normSq} (\sum \operatorname{z} : (\operatorname{Fin} (6 \cdot \operatorname{m}) \to \operatorname{Bool}),\operatorname{graphAmplitude} \operatorname{G} \operatorname{z} \cdot \operatorname{measurementRow} (\operatorname{fun} \cdot \mapsto \operatorname{false}) \theta \operatorname{z}))))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.graphProbability` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines graphProbability.

**Theorem 1.33 (graph sqrt shift).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{G} : (\operatorname{Finset} ((\operatorname{Fin} (6 \cdot \operatorname{m})) \times (\operatorname{Fin} (6 \cdot \operatorname{m}))))), (\forall (\operatorname{d} : (\operatorname{Fin} (6 \cdot \operatorname{m})) \to \mathbb{R}), ((\int \theta,(\operatorname{Real}.\operatorname{sqrt} ((2:\mathbb{R})^{6\cdot\operatorname{m}} \cdot \operatorname{graphProbability} \operatorname{G} (\operatorname{fun} \operatorname{i} \mapsto \theta \operatorname{i} + \operatorname{d} \operatorname{i}))) d \operatorname{uniformAngles} \operatorname{m}) = (\int \theta,(\operatorname{Real}.\operatorname{sqrt} ((2:\mathbb{R})^{6\cdot\operatorname{m}} \cdot \operatorname{graphProbability} \operatorname{G} \theta)) d \operatorname{uniformAngles} \operatorname{m}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.graph_sqrt_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The graph probability is periodic in every angle: its effect-matrix factors are invariant under adding two pi. A finite amplitude bound makes the square-root integrand bounded, so pi_periodic_shift gives invariance of its normalized product-angle integral under arbitrary coordinate shifts.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.W_false_squared`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.angleSplit`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.circuit_amplitude_literal`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.complementEquiv`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.densityProbability`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.factor_nonempty`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.factor_output_graph_probability`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.gate_entry_norm_le_one`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.graphAmplitude`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.graphProbability`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.graph_probability_effect_zero`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.graph_sqrt_shift`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.joint_fractional_bound`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.literal_joint_probability`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.measurementRow`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.normSq_finite_sum`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.normalizedDensity_eq`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.normalizedTwinDensity`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.normalized_density_nonneg`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.normalized_twin_conditional_mean`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.one_qubit_effect_zero`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.reindexedTwinAmplitude`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.reindexed_twin_marginal`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.result`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.retainedEffect`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.retainedRow`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.retainedSplit`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.split_integral`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.twinDensityProbability`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.twinProbability`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.twin_fractional_moment`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.twin_probability_density`
- Dependency: [D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation](../../Entanglement/RandomizedGraphNegativityRefutation.md)
- Dependency: [D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors](HardwareCircuitFactors.md)
