# Hardware Circuit Factors

## Abstract

HardwareCircuitFactors describes the forced-twin mechanism for QPU-restricted IQP circuits.

**Definition 1.1 (connector).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{u} : (\operatorname{Fin} (6 \cdot \operatorname{m}))), (\forall (\operatorname{v} : (\operatorname{Fin} (6 \cdot \operatorname{m}))), (\operatorname{connector} \operatorname{u} \operatorname{v} \iff \operatorname{val}((\operatorname{u}.\operatorname{cast} (\operatorname{Nat}.\operatorname{mul}_{\operatorname{comm}} 6 \operatorname{m})).\operatorname{modNat}) = 5 \land \operatorname{val}((\operatorname{v}.\operatorname{cast} (\operatorname{Nat}.\operatorname{mul}_{\operatorname{comm}} 6 \operatorname{m})).\operatorname{modNat}) = 4 \land \operatorname{val}((\operatorname{v}.\operatorname{cast} (\operatorname{Nat}.\operatorname{mul}_{\operatorname{comm}} 6 \operatorname{m})).\operatorname{divNat}) = \operatorname{Nat}.\operatorname{mod} (\operatorname{val}((\operatorname{u}.\operatorname{cast} (\operatorname{Nat}.\operatorname{mul}_{\operatorname{comm}} 6 \operatorname{m})).\operatorname{divNat}) + 1) \operatorname{m})))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.connector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines connector. Fin.divNat and Fin.modNat give the quotient and remainder after the product-size cast. Nat.div and Nat.mod denote integer division and remainder; every cast displays its target or equality proof.

**Definition 1.2 (hardwareAdj).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{u} : (\operatorname{Fin} (6 \cdot \operatorname{m}))), (\forall (\operatorname{v} : (\operatorname{Fin} (6 \cdot \operatorname{m}))), (\operatorname{hardwareAdj} \operatorname{u} \operatorname{v} \iff \operatorname{u} \neq \operatorname{v} \land ((\operatorname{val}((\operatorname{u}.\operatorname{cast} (\operatorname{Nat}.\operatorname{mul}_{\operatorname{comm}} 6 \operatorname{m})).\operatorname{divNat}) = \operatorname{val}((\operatorname{v}.\operatorname{cast} (\operatorname{Nat}.\operatorname{mul}_{\operatorname{comm}} 6 \operatorname{m})).\operatorname{divNat}) \land \neg ((\operatorname{val}((\operatorname{u}.\operatorname{cast} (\operatorname{Nat}.\operatorname{mul}_{\operatorname{comm}} 6 \operatorname{m})).\operatorname{modNat}) = 4 \land \operatorname{val}((\operatorname{v}.\operatorname{cast} (\operatorname{Nat}.\operatorname{mul}_{\operatorname{comm}} 6 \operatorname{m})).\operatorname{modNat}) = 5) \lor (\operatorname{val}((\operatorname{u}.\operatorname{cast} (\operatorname{Nat}.\operatorname{mul}_{\operatorname{comm}} 6 \operatorname{m})).\operatorname{modNat}) = 5 \land \operatorname{val}((\operatorname{v}.\operatorname{cast} (\operatorname{Nat}.\operatorname{mul}_{\operatorname{comm}} 6 \operatorname{m})).\operatorname{modNat}) = 4))) \lor \operatorname{connector} \operatorname{u} \operatorname{v} \lor \operatorname{connector} \operatorname{v} \operatorname{u}))))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.hardwareAdj` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines hardwareAdj.

**Definition 1.3 (H).**

$$\forall (\operatorname{m} : \mathbb{N}), ((\operatorname{H} \operatorname{m}).\operatorname{Adj} = \operatorname{hardwareAdj})$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.H` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The simple hardware graph has the displayed adjacency: each component is K6 without the edge between vertices 4 and 5, and consecutive blocks have the cyclic connector from 5 to 4.

**Definition 1.4 (hardwareEdges).**

$$\forall (\operatorname{m} : \mathbb{N}), (\operatorname{hardwareEdges} \operatorname{m} = \operatorname{Finset}.\operatorname{univ}.\operatorname{filter} \operatorname{fun} \operatorname{e} \mapsto \operatorname{e}.1.\operatorname{val} < \operatorname{e}.2.\operatorname{val} \land \operatorname{hardwareAdj} \operatorname{e}.1 \operatorname{e}.2)$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.hardwareEdges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines hardwareEdges.

**Definition 1.5 (edgeDegree).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{G} : \operatorname{Finset} ((\operatorname{Fin} (6 \cdot \operatorname{m}) \times \operatorname{Fin} (6 \cdot \operatorname{m})))), (\forall (\operatorname{v} : (\operatorname{Fin} (6 \cdot \operatorname{m}))), (\operatorname{edgeDegree} \operatorname{G} \operatorname{v} = (\operatorname{G}.\operatorname{filter} \operatorname{fun} \operatorname{e} \mapsto \operatorname{v} \in \operatorname{s}(\operatorname{e}.1,\operatorname{e}.2)).\operatorname{card})))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.edgeDegree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines edgeDegree.

**Definition 1.6 (F4).**

$$\forall (\operatorname{m} : \mathbb{N}), (\operatorname{F4} \operatorname{m} = (\operatorname{hardwareEdges} \operatorname{m}).\operatorname{powerset}.\operatorname{filter} \operatorname{fun} \operatorname{G} \mapsto \forall \operatorname{v}, \operatorname{edgeDegree} \operatorname{G} \operatorname{v} = 4)$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.F4` (`✓ std3`).

*Citation.* D. A. Lidar (2025). *Digital-Analog-Digital Quantum Supremacy*. DOI: [10.48550/arXiv.2512.07127](https://doi.org/10.48550/arXiv.2512.07127). URL: <https://arxiv.org/abs/2512.07127v1>.

*Commentary.*

Definition 1, p. 4, verbatim from the source TeX: "Let \mH_n=(\mV_{\mH},\mE_{\mH}) be a fixed simple D-regular hardware graph on n labeled vertices, and let 3\le d\le D be a fixed constant (n-independent). The \emph{d-factors} of a graph \mH are \mF_d(\mH) \equiv \{\mG=(\mV,\mE_{\mG}) : \mE_{\mG}\subseteq \mE_{\mH},\deg_{\mG}(v)=d\ \forall v\in\mV\}. The \emph{QPU-restricted graph ensemble} is the probability space \mathrm{Unif}[\mF_d(\mH_n)] in which, for each run of \UDAD, a graph \mG\in\mF_d(\mH_n) is drawn uniformly at random." Here d is four; ordered endpoint pairs record each undirected edge once, and all four-factors are retained.

**Definition 1.7 (randomLayer).**

$$\forall (\operatorname{m} : \mathbb{N}), \forall (\theta : ((\operatorname{Fin} (6\cdot\operatorname{m})) \to \mathbb{R})), \operatorname{randomLayer} \operatorname{m} \theta = ((\operatorname{tensorOp} (\operatorname{fun} \operatorname{i} \mapsto (\operatorname{hadamard} \cdot \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{PrecessionSpinOneSeparableBound}.\operatorname{rotation} 1 ((\theta \operatorname{i}))))).\operatorname{submatrix} (\operatorname{fun} \operatorname{s} \operatorname{i} \mapsto (\operatorname{if} ((\operatorname{s} \operatorname{i})) \operatorname{then} 1 \operatorname{else} 0)) (\operatorname{fun} \operatorname{z} \operatorname{i} \mapsto (\operatorname{if} ((\operatorname{z} \operatorname{i})) \operatorname{then} 1 \operatorname{else} 0)))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.randomLayer` (`✓ std3`).

*Citation.* D. A. Lidar (2025). *Digital-Analog-Digital Quantum Supremacy*. DOI: [10.48550/arXiv.2512.07127](https://doi.org/10.48550/arXiv.2512.07127). URL: <https://arxiv.org/abs/2512.07127v1>.

*Commentary.*

The displayed expression defines randomLayer.

**Definition 1.8 (HZ).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{G} : \operatorname{Finset} ((\operatorname{Fin} (6 \cdot \operatorname{m}) \times \operatorname{Fin} (6 \cdot \operatorname{m})))), (\forall (\operatorname{z} : (\operatorname{Fin} (6 \cdot \operatorname{m}) \to \operatorname{Bool})), (\operatorname{HZ} \operatorname{G} \operatorname{z} = (\sum \operatorname{i}, (\operatorname{Real}.\operatorname{pi} / 7) \cdot \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumBounds}.\operatorname{MerminMeasurementDependence}.\operatorname{boolSign} (\operatorname{z} \operatorname{i})) + (\operatorname{Real}.\operatorname{pi} / 4) \cdot \sum \operatorname{e} \in \operatorname{G}, \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumBounds}.\operatorname{MerminMeasurementDependence}.\operatorname{boolSign} (\operatorname{z} \operatorname{e}.1) \cdot \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumBounds}.\operatorname{MerminMeasurementDependence}.\operatorname{boolSign} (\operatorname{z} \operatorname{e}.2))))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.HZ` (`✓ std3`).

*Citation.* D. A. Lidar (2025). *Digital-Analog-Digital Quantum Supremacy*. DOI: [10.48550/arXiv.2512.07127](https://doi.org/10.48550/arXiv.2512.07127). URL: <https://arxiv.org/abs/2512.07127v1>.

*Commentary.*

Equation (19) uses the Hamiltonian H prime Z from Eq. (19b): each single-qubit angle is fixed to pi/7, and every selected edge has coupling pi/4. The diagonal entries use the Z eigenvalues of the bit string.

**Definition 1.9 (circuit).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{G} : \operatorname{Finset} (\operatorname{Fin} (6 \cdot \operatorname{m}) \times \operatorname{Fin} (6 \cdot \operatorname{m}))), (\forall (\theta : \operatorname{Fin} (6 \cdot \operatorname{m}) \to \mathbb{R}), (\operatorname{circuit} \operatorname{G} \theta = \operatorname{randomLayer} \operatorname{m} \theta \cdot (\operatorname{Matrix}.\operatorname{diagonal} (\operatorname{fun} \operatorname{z} \mapsto \operatorname{Complex}.\operatorname{exp} (-\operatorname{Complex}.\operatorname{I} \cdot (\operatorname{HZ} \operatorname{G} \operatorname{z} : \mathbb{C})))) \cdot (\operatorname{tensorOp} (\operatorname{fun} \cdot : \operatorname{Fin} (6 \cdot \operatorname{m}) \mapsto \operatorname{hadamard})).\operatorname{submatrix} (\operatorname{fun} (\operatorname{s} : \operatorname{Fin} (6 \cdot \operatorname{m}) \to \operatorname{Bool}) \operatorname{i} \mapsto (\operatorname{if} (\operatorname{s} \operatorname{i}) \operatorname{then} 1 \operatorname{else} 0)) (\operatorname{fun} (\operatorname{z} : \operatorname{Fin} (6 \cdot \operatorname{m}) \to \operatorname{Bool}) \operatorname{i} \mapsto (\operatorname{if} (\operatorname{z} \operatorname{i}) \operatorname{then} 1 \operatorname{else} 0)))))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.circuit` (`✓ std3`).

*Citation.* D. A. Lidar (2025). *Digital-Analog-Digital Quantum Supremacy*. DOI: [10.48550/arXiv.2512.07127](https://doi.org/10.48550/arXiv.2512.07127). URL: <https://arxiv.org/abs/2512.07127v1>.

*Commentary.*

Equation (19), verbatim: \UIQP^{(\theta)} = U_{\mathrm{R}}^{(\theta)} e^{-i H'_Z} W^{\otimes n}. The definition is this literal matrix product, with randomLayer the tensor product of hadamard times rotation 1 theta_i in Bool coordinates.

**Definition 1.10 (outputProbability).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{G} : \operatorname{Finset} ((\operatorname{Fin} (6 \cdot \operatorname{m}) \times \operatorname{Fin} (6 \cdot \operatorname{m})))), (\forall (\theta : (\operatorname{Fin} (6 \cdot \operatorname{m})) \to \mathbb{R}), (\forall (\operatorname{s} : (\operatorname{Fin} (6 \cdot \operatorname{m}) \to \operatorname{Bool})), (\operatorname{outputProbability} \operatorname{G} \theta \operatorname{s} = \operatorname{Complex}.\operatorname{normSq} (\operatorname{circuit} \operatorname{G} \theta \operatorname{s} (\operatorname{fun} \cdot \mapsto \operatorname{false}))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.outputProbability` (`✓ std3`).

*Citation.* D. A. Lidar (2025). *Digital-Analog-Digital Quantum Supremacy*. DOI: [10.48550/arXiv.2512.07127](https://doi.org/10.48550/arXiv.2512.07127). URL: <https://arxiv.org/abs/2512.07127v1>.

*Commentary.*

The probability is the squared modulus of the literal circuit matrix element from the all-false input to the output s.

**Definition 1.11 (uniformAngles).**

$$\forall (\operatorname{m} : \mathbb{N}), (\operatorname{uniformAngles} \operatorname{m} = \operatorname{Measure}.\operatorname{pi} \operatorname{fun} \cdot \mapsto (\operatorname{ProbabilityTheory}.\operatorname{cond} \operatorname{volume} (\operatorname{Set}.\operatorname{Ico} 0 (2 \cdot \operatorname{Real}.\operatorname{pi}))))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.uniformAngles` (`✓ std3`).

*Citation.* D. A. Lidar (2025). *Digital-Analog-Digital Quantum Supremacy*. DOI: [10.48550/arXiv.2512.07127](https://doi.org/10.48550/arXiv.2512.07127). URL: <https://arxiv.org/abs/2512.07127v1>.

*Commentary.*

The angle distribution is specified on p. 4, verbatim from the source TeX: "We choose i.i.d. angles \{\theta_i\}_{i=1}^n uniformly from [0,2\pi),". The displayed product measure expresses the independence of all coordinates.

**Definition 1.12 (joint).**

$$\forall (\operatorname{m} : \mathbb{N}), (\operatorname{joint} \operatorname{m} = ((\operatorname{ProbabilityTheory}.\operatorname{uniformOn} (\operatorname{val}(\operatorname{F4} \operatorname{m})))).\operatorname{prod} (\operatorname{uniformAngles} \operatorname{m}))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.joint` (`✓ std3`).

*Citation.* D. A. Lidar (2025). *Digital-Analog-Digital Quantum Supremacy*. DOI: [10.48550/arXiv.2512.07127](https://doi.org/10.48550/arXiv.2512.07127). URL: <https://arxiv.org/abs/2512.07127v1>.

*Commentary.*

The graph and angles are independent; their joint law is the product measure.

**Definition 1.13 (tailProbability).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{a} : \mathbb{R}), (\forall (\operatorname{s} : (\operatorname{Fin} (6 \cdot \operatorname{m}) \to \operatorname{Bool})), (\operatorname{tailProbability} \operatorname{m} \operatorname{a} \operatorname{s} = (\operatorname{joint} \operatorname{m}).\operatorname{real} \{\omega | \operatorname{a} \cdot ((2 : \mathbb{R})^{6 \cdot \operatorname{m}})^{-1} \leq \operatorname{outputProbability} \omega.1 \omega.2 \operatorname{s}\})))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.tailProbability` (`✓ std3`).

*Citation.* D. A. Lidar (2025). *Digital-Analog-Digital Quantum Supremacy*. DOI: [10.48550/arXiv.2512.07127](https://doi.org/10.48550/arXiv.2512.07127). URL: <https://arxiv.org/abs/2512.07127v1>.

*Commentary.*

The displayed expression defines tailProbability.

**Definition 1.14 (localEdges).**

$$\operatorname{localEdges} = ![(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4),(3,5)]$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.localEdges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed table defines localEdges : Fin 14 → Fin 6 × Fin 6, the fourteen internal edges of K6 with the edge (4,5) removed.

**Definition 1.15 (localDegree).**

$$\forall (\operatorname{M} : \operatorname{Fin} 14 \to \operatorname{Bool}), (\forall (\operatorname{v} : \operatorname{Fin} 6), (\operatorname{localDegree} \operatorname{M} \operatorname{v} = \sum \operatorname{e} : \operatorname{Fin} 14, \operatorname{if} \operatorname{Bool}.\operatorname{and} (\operatorname{M} \operatorname{e}) (\operatorname{Bool}.\operatorname{or} (\operatorname{decide} ((\operatorname{localEdges} \operatorname{e}).1 = \operatorname{v})) (\operatorname{decide} ((\operatorname{localEdges} \operatorname{e}).2 = \operatorname{v}))) \operatorname{then} 1 \operatorname{else} 0))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.localDegree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines localDegree.

**Definition 1.16 (boundaryDegree).**

$$\forall (\operatorname{incoming} : \operatorname{Bool}), (\forall (\operatorname{outgoing} : \operatorname{Bool}), (\forall (\operatorname{v} : \operatorname{Fin} 6), (\operatorname{boundaryDegree} \operatorname{incoming} \operatorname{outgoing} \operatorname{v} = (\operatorname{if} \operatorname{Bool}.\operatorname{and} (\operatorname{decide} (\operatorname{v} = 4)) \operatorname{incoming} \operatorname{then} 1 \operatorname{else} 0) + (\operatorname{if} \operatorname{Bool}.\operatorname{and} (\operatorname{decide} (\operatorname{v} = 5)) \operatorname{outgoing} \operatorname{then} 1 \operatorname{else} 0))))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.boundaryDegree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines boundaryDegree.

**Definition 1.17 (LocalMatching).**

$$\forall (\operatorname{M} : \operatorname{Fin} 14 \to \operatorname{Bool}), (\forall (\operatorname{incoming} : \operatorname{Bool}), (\forall (\operatorname{outgoing} : \operatorname{Bool}), (\operatorname{LocalMatching} \operatorname{M} \operatorname{incoming} \operatorname{outgoing} \iff \forall \operatorname{v}, \operatorname{localDegree} \operatorname{M} \operatorname{v} + \operatorname{boundaryDegree} \operatorname{incoming} \operatorname{outgoing} \operatorname{v} = 1)))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.LocalMatching` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines LocalMatching.

**Definition 1.18 (blockEquiv).**

$$\forall (\operatorname{m} : \mathbb{N}), (\operatorname{blockEquiv} \operatorname{m} = \operatorname{finProdFinEquiv}.\operatorname{trans} (\operatorname{finCongr} (\operatorname{Nat}.\operatorname{mul}_{\operatorname{comm}} \operatorname{m} 6)))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.blockEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines blockEquiv.

**Theorem 1.19 (blockEquiv val).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{i} : \operatorname{Fin} \operatorname{m}), (\forall (\operatorname{v} : \operatorname{Fin} 6), ((\operatorname{blockEquiv} \operatorname{m} (\operatorname{i},\operatorname{v})).\operatorname{val} = 6 \cdot \operatorname{i}.\operatorname{val} + \operatorname{v}.\operatorname{val})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.blockEquiv_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated blockEquiv val relation for the finite twin-pair calculation.

**Theorem 1.20 (component encode).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{i} : \operatorname{Fin} \operatorname{m}), (\forall (\operatorname{v} : \operatorname{Fin} 6), (\operatorname{val}(((\operatorname{blockEquiv} \operatorname{m} (\operatorname{i},\operatorname{v})).\operatorname{cast} (\operatorname{Nat}.\operatorname{mul}_{\operatorname{comm}} 6 \operatorname{m})).\operatorname{divNat}) = \operatorname{i}.\operatorname{val} \land \operatorname{val}(((\operatorname{blockEquiv} \operatorname{m} (\operatorname{i},\operatorname{v})).\operatorname{cast} (\operatorname{Nat}.\operatorname{mul}_{\operatorname{comm}} 6 \operatorname{m})).\operatorname{modNat}) = \operatorname{v}.\operatorname{val})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.block_encode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated component encode relation for the finite twin-pair calculation.

**Definition 1.21 (localNeighbours).**

$$\forall (\operatorname{v} : \operatorname{Fin} 6), (\operatorname{localNeighbours} \operatorname{v} = \operatorname{Finset}.\operatorname{univ}.\operatorname{filter} \operatorname{fun} \operatorname{w} \mapsto \operatorname{v} \neq \operatorname{w} \land \neg ((\operatorname{v} = 4 \land \operatorname{w} = 5) \lor (\operatorname{v} = 5 \land \operatorname{w} = 4)))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.localNeighbours` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines localNeighbours.

**Theorem 1.22 (hardware adj encoded).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{i} : \operatorname{Fin} \operatorname{m}), (\forall (\operatorname{j} : \operatorname{Fin} \operatorname{m}), (\forall (\operatorname{r} : \operatorname{Fin} 6), (\forall (\operatorname{t} : \operatorname{Fin} 6), (\operatorname{hardwareAdj} (\operatorname{blockEquiv} \operatorname{m} (\operatorname{i},\operatorname{r})) (\operatorname{blockEquiv} \operatorname{m} (\operatorname{j},\operatorname{t})) \iff (\operatorname{i} = \operatorname{j} \land \operatorname{t} \in \operatorname{localNeighbours} \operatorname{r}) \lor (\operatorname{r} = 5 \land \operatorname{t} = 4 \land \operatorname{j}.\operatorname{val} = (\operatorname{i}.\operatorname{val} + 1) \operatorname{Nat}.\operatorname{mod} \operatorname{m}) \lor (\operatorname{t} = 5 \land \operatorname{r} = 4 \land \operatorname{i}.\operatorname{val} = (\operatorname{j}.\operatorname{val} + 1) \operatorname{Nat}.\operatorname{mod} \operatorname{m}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.hardware_adj_encoded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated hardware adj encoded relation for the finite twin-pair calculation.

**Theorem 1.23 (cyclic next val).**

$$\forall (\operatorname{m} : \mathbb{N}), ([\operatorname{NeZero} \operatorname{m}] \to ((1 < \operatorname{m}) \to (\forall (\operatorname{i} : \operatorname{Fin} \operatorname{m}), ((\operatorname{i} + 1).\operatorname{val} = (\operatorname{i}.\operatorname{val} + 1) \operatorname{Nat}.\operatorname{mod} \operatorname{m}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.cyclic_next_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated cyclic next val relation for the finite twin-pair calculation.

**Theorem 1.24 (cyclic prev iff).**

$$\forall (\operatorname{m} : \mathbb{N}), ([\operatorname{NeZero} \operatorname{m}] \to ((1 < \operatorname{m}) \to (\forall (\operatorname{i} : \operatorname{Fin} \operatorname{m}), (\forall (\operatorname{j} : \operatorname{Fin} \operatorname{m}), (\operatorname{i}.\operatorname{val} = (\operatorname{j}.\operatorname{val} + 1) \operatorname{Nat}.\operatorname{mod} \operatorname{m} \iff \operatorname{j} = \operatorname{i} - 1)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.cyclic_prev_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated cyclic prev iff relation for the finite twin-pair calculation.

**Theorem 1.25 (cyclic next iff).**

$$\forall (\operatorname{m} : \mathbb{N}), ([\operatorname{NeZero} \operatorname{m}] \to ((1 < \operatorname{m}) \to (\forall (\operatorname{i} : \operatorname{Fin} \operatorname{m}), (\forall (\operatorname{j} : \operatorname{Fin} \operatorname{m}), (\operatorname{j}.\operatorname{val} = (\operatorname{i}.\operatorname{val} + 1) \operatorname{Nat}.\operatorname{mod} \operatorname{m} \iff \operatorname{j} = \operatorname{i} + 1)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.cyclic_next_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated cyclic next iff relation for the finite twin-pair calculation.

**Theorem 1.26 (hardware adj encoded cycle).**

$$\forall (\operatorname{m} : \mathbb{N}), ([\operatorname{NeZero} \operatorname{m}] \to ((1 < \operatorname{m}) \to (\forall (\operatorname{i} : \operatorname{Fin} \operatorname{m}), (\forall (\operatorname{j} : \operatorname{Fin} \operatorname{m}), (\forall (\operatorname{r} : \operatorname{Fin} 6), (\forall (\operatorname{t} : \operatorname{Fin} 6), (\operatorname{hardwareAdj} (\operatorname{blockEquiv} \operatorname{m} (\operatorname{i},\operatorname{r})) (\operatorname{blockEquiv} \operatorname{m} (\operatorname{j},\operatorname{t})) \iff (\operatorname{i} = \operatorname{j} \land \operatorname{t} \in \operatorname{localNeighbours} \operatorname{r}) \lor (\operatorname{r} = 5 \land \operatorname{t} = 4 \land \operatorname{j} = \operatorname{i} + 1) \lor (\operatorname{t} = 5 \land \operatorname{r} = 4 \land \operatorname{j} = \operatorname{i} - 1))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.hardware_adj_encoded_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated hardware adj encoded cycle relation for the finite twin-pair calculation.

**Theorem 1.27 (encoded neighbours card).**

$$\forall (\operatorname{m} : \mathbb{N}), ([\operatorname{NeZero} \operatorname{m}] \to ((1 < \operatorname{m}) \to (\forall (\operatorname{i} : \operatorname{Fin} \operatorname{m}), (\forall (\operatorname{r} : \operatorname{Fin} 6), ((\operatorname{Finset}.\operatorname{univ}.\operatorname{filter} (\operatorname{fun} \operatorname{w} : \operatorname{Fin} \operatorname{m} \times \operatorname{Fin} 6 \mapsto \operatorname{hardwareAdj} (\operatorname{blockEquiv} \operatorname{m} (\operatorname{i},\operatorname{r})) (\operatorname{blockEquiv} \operatorname{m} \operatorname{w}))).\operatorname{card} = 5)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.encoded_neighbours_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated encoded neighbours card relation for the finite twin-pair calculation.

**Theorem 1.28 (orderedEdge hardware).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{u} : (\operatorname{Fin} (6 \cdot \operatorname{m}))), (\forall (\operatorname{v} : (\operatorname{Fin} (6 \cdot \operatorname{m}))), ((\operatorname{hardwareAdj} \operatorname{u} \operatorname{v}) \to ((\operatorname{Sym2}.\operatorname{sortEquiv} \operatorname{s}(\operatorname{u},\operatorname{v})).\operatorname{val} \in \operatorname{hardwareEdges} \operatorname{m}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.orderedEdge_hardware` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated orderedEdge hardware relation for the finite twin-pair calculation.

**Theorem 1.29 (hardware incident card).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{v} : (\operatorname{Fin} (6 \cdot \operatorname{m}))), (\operatorname{edgeDegree} (\operatorname{hardwareEdges} \operatorname{m}) \operatorname{v} = (\operatorname{Finset}.\operatorname{univ}.\operatorname{filter} (\operatorname{fun} \operatorname{w} \mapsto \operatorname{hardwareAdj} \operatorname{v} \operatorname{w})).\operatorname{card}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.hardware_incident_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated hardware incident card relation for the finite twin-pair calculation.

**Theorem 1.30 (hardware degree five).**

$$\forall (\operatorname{m} : \mathbb{N}), ([\operatorname{NeZero} \operatorname{m}] \to ((1 < \operatorname{m}) \to (\forall (\operatorname{v} : (\operatorname{Fin} (6 \cdot \operatorname{m}))), (\operatorname{edgeDegree} (\operatorname{hardwareEdges} \operatorname{m}) \operatorname{v} = 5))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.hardware_degree_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For more than one component the hardware is five-regular, as required by Definition 1 with D=5.

**Theorem 1.31 (factor complement matching).**

$$\forall (\operatorname{m} : \mathbb{N}), ([\operatorname{NeZero} \operatorname{m}] \to ((1 < \operatorname{m}) \to (\forall (\operatorname{G} : \operatorname{Finset} ((\operatorname{Fin} (6 \cdot \operatorname{m}) \times \operatorname{Fin} (6 \cdot \operatorname{m})))), ((\operatorname{G} \in \operatorname{F4} \operatorname{m}) \to (\forall \operatorname{v}, \operatorname{edgeDegree} (\operatorname{hardwareEdges} \operatorname{m} \setminus \operatorname{G}) \operatorname{v} = 1)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.factor_complement_matching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated factor complement matching relation for the finite twin-pair calculation.

**Definition 1.32 (edgeAdj).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{E} : \operatorname{Finset} ((\operatorname{Fin} (6 \cdot \operatorname{m}) \times \operatorname{Fin} (6 \cdot \operatorname{m})))), (\forall (\operatorname{u} : (\operatorname{Fin} (6 \cdot \operatorname{m}))), (\forall (\operatorname{v} : (\operatorname{Fin} (6 \cdot \operatorname{m}))), (\operatorname{edgeAdj} \operatorname{E} \operatorname{u} \operatorname{v} \iff (\operatorname{Sym2}.\operatorname{sortEquiv} \operatorname{s}(\operatorname{u},\operatorname{v})).\operatorname{val} \in \operatorname{E}))))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.edgeAdj` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines edgeAdj.

**Theorem 1.33 (edgeAdj hardware).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{E} : \operatorname{Finset} ((\operatorname{Fin} (6 \cdot \operatorname{m}) \times \operatorname{Fin} (6 \cdot \operatorname{m})))), ((\operatorname{E} \subseteq \operatorname{hardwareEdges} \operatorname{m}) \to (\forall (\operatorname{u} : (\operatorname{Fin} (6 \cdot \operatorname{m}))), (\forall (\operatorname{v} : (\operatorname{Fin} (6 \cdot \operatorname{m}))), ((\operatorname{edgeAdj} \operatorname{E} \operatorname{u} \operatorname{v}) \to (\operatorname{hardwareAdj} \operatorname{u} \operatorname{v}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.edgeAdj_hardware` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated edgeAdj hardware relation for the finite twin-pair calculation.

**Theorem 1.34 (edgeAdj symm).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{E} : \operatorname{Finset} ((\operatorname{Fin} (6 \cdot \operatorname{m}) \times \operatorname{Fin} (6 \cdot \operatorname{m})))), (\forall (\operatorname{u} : (\operatorname{Fin} (6 \cdot \operatorname{m}))), (\forall (\operatorname{v} : (\operatorname{Fin} (6 \cdot \operatorname{m}))), (\operatorname{edgeAdj} \operatorname{E} \operatorname{u} \operatorname{v} \iff \operatorname{edgeAdj} \operatorname{E} \operatorname{v} \operatorname{u}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.edgeAdj_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated edgeAdj symm relation for the finite twin-pair calculation.

**Theorem 1.35 (subset incident card).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{E} : \operatorname{Finset} ((\operatorname{Fin} (6 \cdot \operatorname{m}) \times \operatorname{Fin} (6 \cdot \operatorname{m})))), ((\operatorname{E} \subseteq \operatorname{hardwareEdges} \operatorname{m}) \to (\forall (\operatorname{v} : (\operatorname{Fin} (6 \cdot \operatorname{m}))), (\operatorname{edgeDegree} \operatorname{E} \operatorname{v} = (\operatorname{Finset}.\operatorname{univ}.\operatorname{filter} (\operatorname{fun} \operatorname{w} \mapsto \operatorname{edgeAdj} \operatorname{E} \operatorname{v} \operatorname{w})).\operatorname{card}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.subset_incident_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated subset incident card relation for the finite twin-pair calculation.

**Theorem 1.36 (matching neighbour unique).**

$$\forall (\operatorname{m} : \mathbb{N}), ([\operatorname{NeZero} \operatorname{m}] \to ((1 < \operatorname{m}) \to (\forall (\operatorname{G} : \operatorname{Finset} ((\operatorname{Fin} (6 \cdot \operatorname{m}) \times \operatorname{Fin} (6 \cdot \operatorname{m})))), ((\operatorname{G} \in \operatorname{F4} \operatorname{m}) \to (\forall (\operatorname{v} : (\operatorname{Fin} (6 \cdot \operatorname{m}))), (\exists! \operatorname{w}, \operatorname{edgeAdj} (\operatorname{hardwareEdges} \operatorname{m} \setminus \operatorname{G}) \operatorname{v} \operatorname{w}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.matching_neighbour_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated matching neighbour unique relation for the finite twin-pair calculation.

**Definition 1.37 (localMatchingFlags).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{E} : \operatorname{Finset} ((\operatorname{Fin} (6 \cdot \operatorname{m}) \times \operatorname{Fin} (6 \cdot \operatorname{m})))), (\forall (\operatorname{i} : \operatorname{Fin} \operatorname{m}), (\operatorname{localMatchingFlags} \operatorname{E} \operatorname{i} = \operatorname{fun} \operatorname{e} \mapsto \operatorname{decide} (\operatorname{edgeAdj} \operatorname{E} (\operatorname{blockEquiv} \operatorname{m} (\operatorname{i},(\operatorname{localEdges} \operatorname{e}).1)) (\operatorname{blockEquiv} \operatorname{m} (\operatorname{i},(\operatorname{localEdges} \operatorname{e}).2))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.localMatchingFlags` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines localMatchingFlags.

**Definition 1.38 (connectorFlag).**

$$\forall (\operatorname{m} : \mathbb{N}), ([\operatorname{NeZero} \operatorname{m}] \to (\forall (\operatorname{E} : \operatorname{Finset} ((\operatorname{Fin} (6 \cdot \operatorname{m}) \times \operatorname{Fin} (6 \cdot \operatorname{m})))), (\forall (\operatorname{i} : \operatorname{Fin} \operatorname{m}), (\operatorname{connectorFlag} \operatorname{E} \operatorname{i} = \operatorname{decide} (\operatorname{edgeAdj} \operatorname{E} (\operatorname{blockEquiv} \operatorname{m} (\operatorname{i},5)) (\operatorname{blockEquiv} \operatorname{m} (\operatorname{i}+1,4)))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.connectorFlag` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines connectorFlag.

**Theorem 1.39 (subset degree local).**

$$\forall (\operatorname{m} : \mathbb{N}), ([\operatorname{NeZero} \operatorname{m}] \to ((1 < \operatorname{m}) \to (\forall (\operatorname{E} : \operatorname{Finset} ((\operatorname{Fin} (6 \cdot \operatorname{m}) \times \operatorname{Fin} (6 \cdot \operatorname{m})))), ((\operatorname{E} \subseteq \operatorname{hardwareEdges} \operatorname{m}) \to (\forall (\operatorname{i} : \operatorname{Fin} \operatorname{m}), (\forall (\operatorname{r} : \operatorname{Fin} 6), (\operatorname{edgeDegree} \operatorname{E} (\operatorname{blockEquiv} \operatorname{m} (\operatorname{i},\operatorname{r})) = \operatorname{localDegree} (\operatorname{localMatchingFlags} \operatorname{E} \operatorname{i}) \operatorname{r} + \operatorname{boundaryDegree} (\operatorname{connectorFlag} \operatorname{E} (\operatorname{i}-1)) (\operatorname{connectorFlag} \operatorname{E} \operatorname{i}) \operatorname{r})))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.subset_degree_local` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated subset degree local relation for the finite twin-pair calculation.

**Theorem 1.40 (hardware internal vertex).**

$$\forall (\operatorname{m} : \mathbb{N}), ([\operatorname{NeZero} \operatorname{m}] \to ((1 < \operatorname{m}) \to (\forall (\operatorname{i} : \operatorname{Fin} \operatorname{m}), (\forall (\operatorname{j} : \operatorname{Fin} \operatorname{m}), (\forall (\operatorname{r} : \operatorname{Fin} 6), (\forall (\operatorname{w} : \operatorname{Fin} 6), ((\operatorname{r}.\operatorname{val} < 4) \to (\operatorname{hardwareAdj} (\operatorname{blockEquiv} \operatorname{m} (\operatorname{i},\operatorname{r})) (\operatorname{blockEquiv} \operatorname{m} (\operatorname{j},\operatorname{w})) \iff \operatorname{i} = \operatorname{j} \land \operatorname{w} \neq \operatorname{r}))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.hardware_internal_vertex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated hardware internal vertex relation for the finite twin-pair calculation.

**Theorem 1.41 (factor component twins).**

$$\forall (\operatorname{m} : \mathbb{N}), ([\operatorname{NeZero} \operatorname{m}] \to ((1 < \operatorname{m}) \to (\forall (\operatorname{G} : \operatorname{Finset} ((\operatorname{Fin} (6 \cdot \operatorname{m}) \times \operatorname{Fin} (6 \cdot \operatorname{m})))), ((\operatorname{G} \in \operatorname{F4} \operatorname{m}) \to (\forall (\operatorname{i} : \operatorname{Fin} \operatorname{m}), (\exists \operatorname{r} \operatorname{t} : \operatorname{Fin} 6, \operatorname{r} \neq \operatorname{t} \land (\forall \operatorname{j} \operatorname{w}, \operatorname{edgeAdj} \operatorname{G} (\operatorname{blockEquiv} \operatorname{m} (\operatorname{i},\operatorname{r})) (\operatorname{blockEquiv} \operatorname{m} (\operatorname{j},\operatorname{w})) \iff \operatorname{i} = \operatorname{j} \land \operatorname{w} \neq \operatorname{r} \land \operatorname{w} \neq \operatorname{t}) \land (\forall \operatorname{j} \operatorname{w}, \operatorname{edgeAdj} \operatorname{G} (\operatorname{blockEquiv} \operatorname{m} (\operatorname{i},\operatorname{t})) (\operatorname{blockEquiv} \operatorname{m} (\operatorname{j},\operatorname{w})) \iff \operatorname{i} = \operatorname{j} \land \operatorname{w} \neq \operatorname{r} \land \operatorname{w} \neq \operatorname{t})))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.factor_block_twins` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every four-factor contains, in each hardware component, two nonadjacent vertices with the other four component vertices as their exact common neighbourhood. This forces a positive density of twin pairs independently of the choice of factor.

**Theorem 1.42 (angle integral eq).**

$$\forall (\operatorname{f} : \mathbb{R} \to \mathbb{R}), ((\int \operatorname{x}, \operatorname{f} \operatorname{x} d(\operatorname{ProbabilityTheory}.\operatorname{cond} \operatorname{volume} (\operatorname{Set}.\operatorname{Ico} 0 (2 \cdot \operatorname{Real}.\operatorname{pi})))) = (2 \cdot \operatorname{Real}.\operatorname{pi})^{-1} \cdot \int \operatorname{x} \operatorname{in} (0 : \mathbb{R})..(2 \cdot \operatorname{Real}.\operatorname{pi}), \operatorname{f} \operatorname{x})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.angle_integral_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The conditional Lebesgue integral is the interval integral divided by the interval length.

**Theorem 1.43 (angle integrable of continuous).**

$$\forall (\operatorname{f} : \mathbb{R} \to \mathbb{R}), ((\operatorname{Continuous} \operatorname{f}) \to (\operatorname{Integrable} \operatorname{f} (\operatorname{ProbabilityTheory}.\operatorname{cond} \operatorname{volume} (\operatorname{Set}.\operatorname{Ico} 0 (2 \cdot \operatorname{Real}.\operatorname{pi})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.angle_integrable_of_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A continuous real function is integrable over the normalized finite angle interval.

**Theorem 1.44 (angle cos mean).**

$$(\int \operatorname{x}, \operatorname{Real}.\operatorname{cos} \operatorname{x} d(\operatorname{ProbabilityTheory}.\operatorname{cond} \operatorname{volume} (\operatorname{Set}.\operatorname{Ico} 0 (2 \cdot \operatorname{Real}.\operatorname{pi})))) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.angle_cos_mean` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized cosine integral over a full period vanishes.

**Definition 1.45 (pairAngle).**

$$\operatorname{pairAngle} = (\operatorname{ProbabilityTheory}.\operatorname{cond} \operatorname{volume} (\operatorname{Set}.\operatorname{Ico} 0 (2 \cdot \operatorname{Real}.\operatorname{pi}))).\operatorname{prod} (\operatorname{ProbabilityTheory}.\operatorname{cond} \operatorname{volume} (\operatorname{Set}.\operatorname{Ico} 0 (2 \cdot \operatorname{Real}.\operatorname{pi})))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.pairAngle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines pairAngle.

**Definition 1.46 (pairCos).**

$$\forall (\operatorname{x} : \mathbb{R} \times \mathbb{R}), (\operatorname{pairCos} \operatorname{x} = \operatorname{Real}.\operatorname{cos} \operatorname{x}.1 \cdot \operatorname{Real}.\operatorname{cos} \operatorname{x}.2)$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.pairCos` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines pairCos.

**Theorem 1.47 (fractional markov).**

$$\forall (\operatorname{A} : \operatorname{Type}), ([\operatorname{MeasurableSpace} \operatorname{A}] \to (\forall (\mu : \operatorname{Measure} \operatorname{A}), ([\operatorname{IsProbabilityMeasure} \mu] \to (\forall (\operatorname{Z} : \operatorname{A} \to \mathbb{R}), ((\forall \operatorname{x}, 0 \leq \operatorname{Z} \operatorname{x}) \to ((\operatorname{Integrable} (\operatorname{fun} \operatorname{x} \mapsto \operatorname{Real}.\operatorname{sqrt} (\operatorname{Z} \operatorname{x})) \mu) \to (\forall (\operatorname{m} : \mathbb{N}), (((\int \operatorname{x}, \operatorname{Real}.\operatorname{sqrt} (\operatorname{Z} \operatorname{x}) d\mu) \leq (47 / 48 : \mathbb{R})^{\operatorname{m}}) \to (\forall (\operatorname{a} : \mathbb{R}), ((0 < \operatorname{a}) \to (\mu.\operatorname{real} \{\operatorname{x} | \operatorname{a} \leq \operatorname{Z} \operatorname{x}\} \leq (\operatorname{Real}.\operatorname{sqrt} \operatorname{a})^{-1} \cdot (47 / 48 : \mathbb{R})^{\operatorname{m}})))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.fractional_markov` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated fractional markov relation for the finite twin-pair calculation.

**Theorem 1.48 (eventual tail bound).**

$$\forall (\operatorname{a} : \mathbb{R}), (\forall (\operatorname{b} : \mathbb{R}), ((0 < \operatorname{a}) \to ((0 < \operatorname{b}) \to (\exists \operatorname{m} : \mathbb{N}, 3 \leq \operatorname{m} \land (\operatorname{Real}.\operatorname{sqrt} \operatorname{a})^{-1} \cdot (47 / 48 : \mathbb{R})^{\operatorname{m}} < \operatorname{b}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.eventual_tail_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated eventual tail bound relation for the finite twin-pair calculation.

**Theorem 1.49 (normalized periodic shift).**

$$\forall (\operatorname{f} : \mathbb{R} \to \mathbb{R}), ((\operatorname{Function}.\operatorname{Periodic} \operatorname{f} (2 \cdot \operatorname{Real}.\operatorname{pi})) \to (\forall (\operatorname{d} : \mathbb{R}), ((\int \operatorname{x}, \operatorname{f} (\operatorname{x} + \operatorname{d}) d(\operatorname{ProbabilityTheory}.\operatorname{cond} \operatorname{volume} (\operatorname{Set}.\operatorname{Ico} 0 (2 \cdot \operatorname{Real}.\operatorname{pi})))) = \int \operatorname{x}, \operatorname{f} \operatorname{x} d(\operatorname{ProbabilityTheory}.\operatorname{cond} \operatorname{volume} (\operatorname{Set}.\operatorname{Ico} 0 (2 \cdot \operatorname{Real}.\operatorname{pi}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.normalized_periodic_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated normalized periodic shift relation for the finite twin-pair calculation.

**Theorem 1.50 (conditional fractional moment).**

$$\forall (\operatorname{Y} : \operatorname{Type}), ([\operatorname{MeasurableSpace} \operatorname{Y}] \to (\forall (\nu : \operatorname{Measure} \operatorname{Y}), ([\operatorname{IsProbabilityMeasure} \nu] \to (\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{Z} : (\operatorname{Fin} \operatorname{m} \to (\mathbb{R} \times \mathbb{R})) \times \operatorname{Y} \to \mathbb{R}), ((\forall \operatorname{w}, 0 \leq \operatorname{Z} \operatorname{w}) \to ((\forall \operatorname{x}, \operatorname{Integrable} (\operatorname{fun} \operatorname{y} \mapsto \operatorname{Z} (\operatorname{x}, \operatorname{y})) \nu \land \operatorname{Integrable} (\operatorname{fun} \operatorname{y} \mapsto \operatorname{Real}.\operatorname{sqrt} (\operatorname{Z} (\operatorname{x}, \operatorname{y}))) \nu) \to ((\operatorname{Integrable} (\operatorname{fun} \operatorname{w} \mapsto \operatorname{Real}.\operatorname{sqrt} (\operatorname{Z} \operatorname{w})) ((\operatorname{Measure}.\operatorname{pi} \operatorname{fun} \cdot : \operatorname{Fin} \operatorname{m} \mapsto \operatorname{pairAngle}).\operatorname{prod} \nu)) \to ((\forall \operatorname{x}, (\int \operatorname{y}, \operatorname{Z} (\operatorname{x}, \operatorname{y}) d\nu) = \prod \operatorname{i}, (1 + \operatorname{pairCos} (\operatorname{x} \operatorname{i}))) \to ((\int \operatorname{w}, \operatorname{Real}.\operatorname{sqrt} (\operatorname{Z} \operatorname{w}) d((\operatorname{Measure}.\operatorname{pi} \operatorname{fun} \cdot : \operatorname{Fin} \operatorname{m} \mapsto \operatorname{pairAngle}).\operatorname{prod} \nu)) \leq (47 / 48 : \mathbb{R})^{\operatorname{m}}))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.conditional_fractional_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated conditional fractional moment relation for the finite twin-pair calculation.

**Theorem 1.51 (pi periodic shift).**

$$\forall (\operatorname{n} : \mathbb{N}), (\forall (\operatorname{f} : (\operatorname{Fin} \operatorname{n} \to \mathbb{R}) \to \mathbb{R}), ((\operatorname{Continuous} \operatorname{f}) \to (\forall (\operatorname{C} : \mathbb{R}), ((\forall \operatorname{x}, \Vert\operatorname{f} \operatorname{x}\Vert \leq \operatorname{C}) \to ((\forall \operatorname{x} \operatorname{i}, \operatorname{Function}.\operatorname{Periodic} (\operatorname{fun} \operatorname{t} \mapsto \operatorname{f} (\operatorname{Function}.\operatorname{update} \operatorname{x} \operatorname{i} \operatorname{t})) (2 \cdot \operatorname{Real}.\operatorname{pi})) \to (\forall (\operatorname{d} : \operatorname{Fin} \operatorname{n} \to \mathbb{R}), ((\int \operatorname{x}, \operatorname{f} (\operatorname{fun} \operatorname{i} \mapsto \operatorname{x} \operatorname{i} + \operatorname{d} \operatorname{i}) d\operatorname{Measure}.\operatorname{pi} (\operatorname{fun} \cdot \mapsto (\operatorname{ProbabilityTheory}.\operatorname{cond} \operatorname{volume} (\operatorname{Set}.\operatorname{Ico} 0 (2 \cdot \operatorname{Real}.\operatorname{pi}))))) = \int \operatorname{x}, \operatorname{f} \operatorname{x} d\operatorname{Measure}.\operatorname{pi} (\operatorname{fun} \cdot \mapsto (\operatorname{ProbabilityTheory}.\operatorname{cond} \operatorname{volume} (\operatorname{Set}.\operatorname{Ico} 0 (2 \cdot \operatorname{Real}.\operatorname{pi})))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.pi_periodic_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A bounded continuous function that is periodic in each coordinate has the same normalized product-angle integral after any fixed coordinate shift. The proof integrates one coordinate at a time.

**Theorem 1.52 (sign product).**

$$\forall (\operatorname{b} : \operatorname{Bool}), (\forall (\operatorname{c} : \operatorname{Bool}), (\operatorname{Int}.\operatorname{negOnePow} ((\operatorname{b}.\operatorname{toNat}) : \mathbb{Z}) \times \operatorname{Int}.\operatorname{negOnePow} ((\operatorname{c}.\operatorname{toNat}) : \mathbb{Z}) = \operatorname{Int}.\operatorname{negOnePow} (((\operatorname{Bool}.\operatorname{xor} \operatorname{b} \operatorname{c}).\operatorname{toNat}) : \mathbb{Z})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.sign_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the indicated sign product relation for the finite twin-pair calculation.

**Definition 1.53 (twinPhase).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{qC} : (\operatorname{Fin} \operatorname{m} \to (\operatorname{Fin} 4 \to \operatorname{Bool})) \to \operatorname{Bool}), (\forall (\operatorname{x} : \operatorname{Fin} \operatorname{m} \to \operatorname{Bool} \times \operatorname{Bool}), (\forall (\operatorname{y} : (\operatorname{Fin} \operatorname{m} \to (\operatorname{Fin} 4 \to \operatorname{Bool}))), (\operatorname{twinPhase} \operatorname{m} \operatorname{qC} \operatorname{x} \operatorname{y} = \operatorname{Int}.\operatorname{negOnePow} (((\operatorname{qC} \operatorname{y}).\operatorname{toNat}) : \mathbb{Z}) \cdot \prod \operatorname{i}, \operatorname{Int}.\operatorname{negOnePow} (((\operatorname{Bool}.\operatorname{and} (\operatorname{Bool}.\operatorname{xor} (\operatorname{x} \operatorname{i}).1 (\operatorname{x} \operatorname{i}).2) (\operatorname{List}.\operatorname{foldl} \operatorname{Bool}.\operatorname{xor} ((\operatorname{y} \operatorname{i}) 0) [((\operatorname{y} \operatorname{i}) 1), ((\operatorname{y} \operatorname{i}) 2), ((\operatorname{y} \operatorname{i}) 3)])).\operatorname{toNat}) : \mathbb{Z})))))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.twinPhase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines twinPhase. The three-element List.foldl starts with the first bit and applies Bool.xor to the remaining bits in order.

**Definition 1.54 (twinAmplitude).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{qC} : (\operatorname{Fin} \operatorname{m} \to (\operatorname{Fin} 4 \to \operatorname{Bool})) \to \operatorname{Bool}), (\forall (\operatorname{xy} : (\operatorname{Fin} \operatorname{m} \to \operatorname{Bool} \times \operatorname{Bool}) \times (\operatorname{Fin} \operatorname{m} \to (\operatorname{Fin} 4 \to \operatorname{Bool}))), (\operatorname{twinAmplitude} \operatorname{m} \operatorname{qC} \operatorname{xy} = ((\left((2 : \mathbb{R})^{-1}\right)^{3 \cdot \operatorname{m}} : \mathbb{R}) : \mathbb{C}) \cdot (\operatorname{twinPhase} \operatorname{m} \operatorname{qC} \operatorname{xy}.1 \operatorname{xy}.2 : \mathbb{C}))))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.twinAmplitude` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines twinAmplitude.

**Theorem 1.55 (twin density tensor).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{qC} : (\operatorname{Fin} \operatorname{m} \to (\operatorname{Fin} 4 \to \operatorname{Bool})) \to \operatorname{Bool}), (\forall (\operatorname{x} : \operatorname{Fin} \operatorname{m} \to \operatorname{Bool} \times \operatorname{Bool}), (\forall (\operatorname{x}' : \operatorname{Fin} \operatorname{m} \to \operatorname{Bool} \times \operatorname{Bool}), (\operatorname{partialTraceRight} (\operatorname{Matrix}.\operatorname{vecMulVec} (\operatorname{twinAmplitude} \operatorname{m} \operatorname{qC}) (\operatorname{star} (\operatorname{twinAmplitude} \operatorname{m} \operatorname{qC}))) \operatorname{x} \operatorname{x}' = \prod \operatorname{i}, \operatorname{if} (\operatorname{Bool}.\operatorname{xor} (\operatorname{x} \operatorname{i}).1 (\operatorname{x} \operatorname{i}).2) = (\operatorname{Bool}.\operatorname{xor} (\operatorname{x}' \operatorname{i}).1 (\operatorname{x}' \operatorname{i}).2) \operatorname{then} (1 / 4 : \mathbb{C}) \operatorname{else} 0))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.twin_density_tensor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complement phase cancels in the Gram sum. The retained density matrix is the exact product of the four-dimensional pair matrices (I4 + X tensor X)/4. The variable qC is a function of the entire complementary bit configuration, so its type is (Fin m -> Fin 4 -> Bool) -> Bool.

**Lemma 1.56 (effect entry).**

$$\forall (\alpha : \mathbb{R}), (\forall (\operatorname{r} : \operatorname{Bool}), (\forall (\operatorname{r}' : \operatorname{Bool}), (\operatorname{effect} \alpha \operatorname{r} \operatorname{r}' = \operatorname{if} \operatorname{r} = \operatorname{r}' \operatorname{then} 1 / 2 \operatorname{else} ((\operatorname{Real}.\operatorname{cos} \alpha : \mathbb{C}) + (\operatorname{if} \operatorname{r} \operatorname{then} -1 \operatorname{else} 1) \cdot \operatorname{Complex}.\operatorname{I} \cdot (\operatorname{Real}.\operatorname{sin} \alpha : \mathbb{C})) / 2)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.effect_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The gate-row projector has the displayed trigonometric entries.

**Definition 1.57 (effect).**

$$\forall (\alpha : \mathbb{R}), \operatorname{effect} \alpha = (\operatorname{Matrix}.\operatorname{vecMulVec} (\operatorname{fun} \operatorname{r} \mapsto (\operatorname{star} ((\operatorname{hadamard} \cdot \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{PrecessionSpinOneSeparableBound}.\operatorname{rotation} 1 (\alpha)) 0 (\operatorname{if} (\operatorname{r}) \operatorname{then} 1 \operatorname{else} 0)))) (\operatorname{star} (\operatorname{fun} \operatorname{r} \mapsto (\operatorname{star} ((\operatorname{hadamard} \cdot \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{PrecessionSpinOneSeparableBound}.\operatorname{rotation} 1 (\alpha)) 0 (\operatorname{if} (\operatorname{r}) \operatorname{then} 1 \operatorname{else} 0))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.effect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines effect.

**Lemma 1.58 (pair density entry).**

$$\forall (\operatorname{x} : \operatorname{Bool} \times \operatorname{Bool}), (\forall (\operatorname{x}' : \operatorname{Bool} \times \operatorname{Bool}), (\operatorname{pairDensity} \operatorname{x} \operatorname{x}' = \operatorname{if} (\operatorname{Bool}.\operatorname{xor} \operatorname{x}.1 \operatorname{x}.2) = (\operatorname{Bool}.\operatorname{xor} \operatorname{x}'.1 \operatorname{x}'.2) \operatorname{then} 1 / 4 \operatorname{else} 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.pair_density_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two-qubit density matrix retains exactly equal parity indices.

**Definition 1.59 (pairDensity).**

$$\operatorname{pairDensity} = (1 / 4 : \mathbb{C}) \cdot ((1 : \operatorname{Matrix} (\operatorname{Bool} \times \operatorname{Bool}) (\operatorname{Bool} \times \operatorname{Bool}) \mathbb{C}) + ((\operatorname{tensorOp} (\operatorname{fun} (\cdot : (\operatorname{Fin} 2)) \mapsto \operatorname{qubitX})).\operatorname{submatrix} (\operatorname{fun} (\operatorname{x} : (\operatorname{Bool} \times \operatorname{Bool})) \mapsto ![(\operatorname{if} (\operatorname{x}.1) \operatorname{then} 1 \operatorname{else} 0), (\operatorname{if} (\operatorname{x}.2) \operatorname{then} 1 \operatorname{else} 0)]) (\operatorname{fun} (\operatorname{x} : (\operatorname{Bool} \times \operatorname{Bool})) \mapsto ![(\operatorname{if} (\operatorname{x}.1) \operatorname{then} 1 \operatorname{else} 0), (\operatorname{if} (\operatorname{x}.2) \operatorname{then} 1 \operatorname{else} 0)])))$$

*Formalization.* `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.pairDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines pairDensity.

**Theorem 1.60 (measurement tensor).**

$$\forall (\operatorname{m} : \mathbb{N}), (\forall (\operatorname{alpha} : \operatorname{Fin} \operatorname{m} \to \mathbb{R}), (\forall (\operatorname{beta} : \operatorname{Fin} \operatorname{m} \to \mathbb{R}), ((\sum \operatorname{x} : (\operatorname{Fin} \operatorname{m} \to (\operatorname{Bool} \times \operatorname{Bool})), \sum \operatorname{x}' : (\operatorname{Fin} \operatorname{m} \to (\operatorname{Bool} \times \operatorname{Bool})), \prod \operatorname{i}, \operatorname{pairDensity} (\operatorname{x} \operatorname{i}) (\operatorname{x}' \operatorname{i}) \cdot \operatorname{effect} (\operatorname{alpha} \operatorname{i}) (\operatorname{x} \operatorname{i}).1 (\operatorname{x}' \operatorname{i}).1 \cdot \operatorname{effect} (\operatorname{beta} \operatorname{i}) (\operatorname{x} \operatorname{i}).2 (\operatorname{x}' \operatorname{i}).2) = (\prod \operatorname{i}, (((1 + \operatorname{Real}.\operatorname{cos} (\operatorname{alpha} \operatorname{i}) \cdot \operatorname{Real}.\operatorname{cos} (\operatorname{beta} \operatorname{i})) / 4 : \mathbb{R}) : \mathbb{C})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.measurement_tensor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement supplies the finite product measurement tensor used by the twin marginal calculation.

**Theorem 1.61 (effect integrable).**

$$\forall (\operatorname{r} : \operatorname{Bool}), (\forall (\operatorname{r}' : \operatorname{Bool}), (\operatorname{Integrable} (\operatorname{fun} \operatorname{alpha} \mapsto \operatorname{effect} \operatorname{alpha} \operatorname{r} \operatorname{r}') (\operatorname{ProbabilityTheory}.\operatorname{cond} \operatorname{volume} (\operatorname{Set}.\operatorname{Ico} 0 (2 \cdot \operatorname{Real}.\operatorname{pi})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.effect_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The single-qubit effect is integrable under the normalized angle measure.

**Theorem 1.62 (complementary effect mean).**

$$\forall (\operatorname{k} : \mathbb{N}), (\forall (\operatorname{z} : \operatorname{Fin} \operatorname{k} \to \operatorname{Bool}), (\forall (\operatorname{z}' : \operatorname{Fin} \operatorname{k} \to \operatorname{Bool}), ((\int \operatorname{alpha}, (\prod \operatorname{i}, (\operatorname{effect} (\operatorname{alpha} \operatorname{i}) (\operatorname{z} \operatorname{i}) (\operatorname{z}' \operatorname{i}))) d (\operatorname{Measure}.\operatorname{pi} \operatorname{fun} \cdot : \operatorname{Fin} \operatorname{k} \mapsto (\operatorname{ProbabilityTheory}.\operatorname{cond} \operatorname{volume} (\operatorname{Set}.\operatorname{Ico} 0 (2 \cdot \operatorname{Real}.\operatorname{pi}))))) = (\prod \operatorname{i}, (\operatorname{if} (\operatorname{z} \operatorname{i} = \operatorname{z}' \operatorname{i}) \operatorname{then} (1 / 2 : \mathbb{C}) \operatorname{else} 0)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.complementary_effect_mean` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product angle integral of complementary single-qubit effects factors into the corresponding diagonal means.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.F4`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.H`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.HZ`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.LocalMatching`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.angle_cos_mean`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.angle_integrable_of_continuous`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.angle_integral_eq`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.blockEquiv`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.blockEquiv_val`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.block_encode`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.boundaryDegree`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.circuit`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.complementary_effect_mean`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.conditional_fractional_moment`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.connector`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.connectorFlag`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.cyclic_next_iff`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.cyclic_next_val`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.cyclic_prev_iff`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.edgeAdj`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.edgeAdj_hardware`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.edgeAdj_symm`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.edgeDegree`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.effect`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.effect_entry`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.effect_integrable`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.encoded_neighbours_card`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.eventual_tail_bound`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.factor_block_twins`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.factor_complement_matching`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.fractional_markov`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.hardwareAdj`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.hardwareEdges`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.hardware_adj_encoded`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.hardware_adj_encoded_cycle`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.hardware_degree_five`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.hardware_incident_card`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.hardware_internal_vertex`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.joint`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.localDegree`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.localEdges`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.localMatchingFlags`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.localNeighbours`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.matching_neighbour_unique`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.measurement_tensor`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.normalized_periodic_shift`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.orderedEdge_hardware`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.outputProbability`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.pairAngle`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.pairCos`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.pairDensity`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.pair_density_entry`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.pi_periodic_shift`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.randomLayer`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.sign_product`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.subset_degree_local`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.subset_incident_card`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.tailProbability`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.twinAmplitude`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.twinPhase`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.twin_density_tensor`
- Truth anchor: `D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors.uniformAngles`
- Dependency: [D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound](../../Entanglement/PrecessionSpinOneSeparableBound.md)
- Dependency: [D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence](../../Information/BinaryStabilizerLocalInequivalence.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/QuantumBounds/MerminMeasurementDependence/Model](../../../QuantumBounds/MerminMeasurementDependence/Model.md)
