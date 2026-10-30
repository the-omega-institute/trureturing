# WassersteinComplexityNonconvex

## Abstract

A qubit dephasing midpoint refutes convexity of Wasserstein complexity.

**Theorem 1.1 (trace_sqrt_sq_le_two).**

$$\forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; (\operatorname{CoPRelativeQuantumnessRefutation}.\operatorname{IsDensity}\left(rho\right)) \Rightarrow (\operatorname{Complex}.\operatorname{re}\left(\operatorname{Matrix}.\operatorname{trace}\left(\operatorname{CFC}.\operatorname{sqrt}\left(rho\right)\right)\right)^{2} \le 2)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/WassersteinComplexityNonconvex.trace_sqrt_sq_le_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every two-dimensional density matrix, the square of the real trace of its positive square root is at most two.

**Theorem 1.2 (pure_diag_coupling).**

$$\forall omega \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall P \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; (P \in \operatorname{QubitWassersteinCouplings}.\operatorname{couplings}\left(\operatorname{ProjectedUnistochasticDynamics}.\operatorname{diagonalState}\left(![1, 0]\right), omega\right)) \Rightarrow (P = \operatorname{Matrix}.\operatorname{kronecker}\left(omega, \operatorname{Matrix}.\operatorname{transpose}\left(\operatorname{ProjectedUnistochasticDynamics}.\operatorname{diagonalState}\left(![1, 0]\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/WassersteinComplexityNonconvex.pure_diag_coupling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A coupling whose prescribed transposed marginal is the pure zero state factors as the other marginal tensor that pure state.

**Definition 1.3 (claim).**

$$(\operatorname{claim}) \Leftrightarrow (\forall d \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall A \in \operatorname{Fin}\left(k\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\forall j \in \operatorname{Fin}\left(k\right),\; \operatorname{Matrix}.\operatorname{IsHermitian}\left(A\left(j\right)\right)) \Rightarrow (\forall Phi1 \in \operatorname{LinearMap}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right),\; \forall Phi2 \in \operatorname{LinearMap}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right),\; (\operatorname{CoPRelativeQuantumnessRefutation}.\operatorname{IsCPTP}\left(Phi1\right)) \Rightarrow ((\operatorname{CoPRelativeQuantumnessRefutation}.\operatorname{IsCPTP}\left(Phi2\right)) \Rightarrow (\forall s \in \mathbb{R},\; (0 \le s) \Rightarrow ((s \le 1) \Rightarrow (\operatorname{CW}\left(A, (s) \cdot (Phi1) + (1 - s) \cdot (Phi2)\right) \le (s) \cdot (\operatorname{CW}\left(A, Phi1\right)) + (1 - s) \cdot (\operatorname{CW}\left(A, Phi2\right))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/WassersteinComplexityNonconvex.claim` (`✓ std3`).

*Citation.* G. Bunth; J. Pitrik; T. Titkos; D. Virosztek (2024). *On the metric property of quantum Wasserstein divergences*. DOI: [10.1103/PhysRevA.110.022211](https://doi.org/10.1103/PhysRevA.110.022211). URL: <https://arxiv.org/abs/2402.13150v4>.

*Commentary.*

Source §5.1, PDF p. 18, verbatim: “We note that whether the Wasserstein complexity (37) is convex or not is an open question.” This is the universal convexity question for every finite dimension and finite Hermitian observable family, CPTP endpoints and a real mixture weight in [0,1]. The literal d=0 case is retained.

**Definition 1.4 (phaseU).**

$$\forall e \in \mathbb{R},\; \operatorname{phaseU}\left(e\right) = \operatorname{Matrix}.\operatorname{diagonal}\left(![\frac{\operatorname{Complex}.\operatorname{ofReal}\left(\operatorname{Real}.\operatorname{sqrt}\left(3\right)\right) + (\operatorname{Complex}.\operatorname{ofReal}\left(e\right)) \cdot (\operatorname{Complex}.\operatorname{I})}{2}, \frac{\operatorname{Complex}.\operatorname{ofReal}\left(\operatorname{Real}.\operatorname{sqrt}\left(3\right)\right) - (\operatorname{Complex}.\operatorname{ofReal}\left(e\right)) \cdot (\operatorname{Complex}.\operatorname{I})}{2}]\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/WassersteinComplexityNonconvex.phaseU` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth; J. Pitrik; T. Titkos; D. Virosztek (2024). *On the metric property of quantum Wasserstein divergences*. DOI: [10.1103/PhysRevA.110.022211](https://doi.org/10.1103/PhysRevA.110.022211). URL: <https://arxiv.org/abs/2402.13150v4>.

*Commentary.*

At the dephasing parameter t=1/4 the phase matrices are diagonal with entries (sqrt 3 plus or minus i e)/2.

**Definition 1.5 (Phi).**

$$\forall e \in \mathbb{R},\; \forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{Phi}\left(e, rho\right) = \operatorname{ProjectedUnistochasticDynamics}.\operatorname{unitaryEvolution}\left(\operatorname{phaseU}\left(e\right), rho\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/WassersteinComplexityNonconvex.Phi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth; J. Pitrik; T. Titkos; D. Virosztek (2024). *On the metric property of quantum Wasserstein divergences*. DOI: [10.1103/PhysRevA.110.022211](https://doi.org/10.1103/PhysRevA.110.022211). URL: <https://arxiv.org/abs/2402.13150v4>.

*Commentary.*

Phi e is the complex-linear conjugation map by phaseU e; the endpoints have e=1 and e=-1.

**Definition 1.6 (AdZ).**

$$\forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{AdZ}\left(rho\right) = ((\operatorname{FiniteDimensional}.\operatorname{qubitZ}) \cdot (rho)) \cdot (\operatorname{FiniteDimensional}.\operatorname{qubitZ})$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/WassersteinComplexityNonconvex.AdZ` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth; J. Pitrik; T. Titkos; D. Virosztek (2024). *On the metric property of quantum Wasserstein divergences*. DOI: [10.1103/PhysRevA.110.022211](https://doi.org/10.1103/PhysRevA.110.022211). URL: <https://arxiv.org/abs/2402.13150v4>.

*Commentary.*

AdZ is the complex-linear conjugation map by the frozen qubitZ.

**Definition 1.7 (Psi).**

$$\operatorname{Psi} = (\frac{3}{4}) \cdot (\operatorname{LinearMap}.\operatorname{id}) + (\frac{1}{4}) \cdot (\operatorname{AdZ})$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/WassersteinComplexityNonconvex.Psi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth; J. Pitrik; T. Titkos; D. Virosztek (2024). *On the metric property of quantum Wasserstein divergences*. DOI: [10.1103/PhysRevA.110.022211](https://doi.org/10.1103/PhysRevA.110.022211). URL: <https://arxiv.org/abs/2402.13150v4>.

*Commentary.*

Psi is the identity/dephasing mixture with t=1/4. The endpoint channel mixture weight is s=1/2.

**Theorem 1.8 (result).**

$$\neg (\forall d \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall A \in \operatorname{Fin}\left(k\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\forall j \in \operatorname{Fin}\left(k\right),\; \operatorname{Matrix}.\operatorname{IsHermitian}\left(A\left(j\right)\right)) \Rightarrow (\forall Phi1 \in \operatorname{LinearMap}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right),\; \forall Phi2 \in \operatorname{LinearMap}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right),\; (\operatorname{CoPRelativeQuantumnessRefutation}.\operatorname{IsCPTP}\left(Phi1\right)) \Rightarrow ((\operatorname{CoPRelativeQuantumnessRefutation}.\operatorname{IsCPTP}\left(Phi2\right)) \Rightarrow (\forall s \in \mathbb{R},\; (0 \le s) \Rightarrow ((s \le 1) \Rightarrow (\operatorname{CW}\left(A, (s) \cdot (Phi1) + (1 - s) \cdot (Phi2)\right) \le (s) \cdot (\operatorname{CW}\left(A, Phi1\right)) + (1 - s) \cdot (\operatorname{CW}\left(A, Phi2\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/WassersteinComplexityNonconvex.result` (`✓ std3`). ∎

*Resolves.* `Problems/bunth-pitrik-titkos-virosztek-2024-wasserstein-complexity-convexity` (refuted) by `D5/S3/Quantum/QuantumChannels/WassersteinComplexityNonconvex.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bunth-pitrik-titkos-virosztek-2024-wasserstein-complexity-convexity","declaration_gid":"D5/S3/Quantum/QuantumChannels/WassersteinComplexityNonconvex.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth; J. Pitrik; T. Titkos; D. Virosztek (2024). *On the metric property of quantum Wasserstein divergences*. DOI: [10.1103/PhysRevA.110.022211](https://doi.org/10.1103/PhysRevA.110.022211). URL: <https://arxiv.org/abs/2402.13150v4>.

*Commentary.*

For the channels Φ₊ and Φ₋ at t=1/4 and their midpoint Ψ at s=1/2, the endpoint bound is C_W(Φ₊), C_W(Φ₋) ≤ √2 while C_W(Ψ) ≥ √(1+√3), with √(1+√3) > √2, so the midpoint value is strictly larger than the endpoint bound.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/WassersteinComplexityNonconvex.AdZ`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/WassersteinComplexityNonconvex.Phi`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/WassersteinComplexityNonconvex.Psi`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/WassersteinComplexityNonconvex.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/WassersteinComplexityNonconvex.phaseU`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/WassersteinComplexityNonconvex.pure_diag_coupling`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/WassersteinComplexityNonconvex.result`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/WassersteinComplexityNonconvex.trace_sqrt_sq_le_two`
- Dependency: [D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics](../Decoherence/ProjectedUnistochasticDynamics.md)
- Dependency: [D5/S3/Quantum/Dynamics/PositivePauliClockOrder](../Dynamics/PositivePauliClockOrder.md)
- Dependency: [D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation](../Entanglement/NandiMutualPredictabilityLOCCRefutation.md)
- Dependency: [D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction](../Entanglement/SteeringEllipsoidFullyEntangledFraction.md)
- Dependency: [D5/S3/Quantum/FiniteDimensional](../FiniteDimensional.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence](../Information/BinaryStabilizerLocalInequivalence.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence](../Information/StabilizerPairLocalUnitaryInequivalence.md)
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../Matrix/CartesianVariance.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings](QubitWassersteinCouplings.md)
- Dependency: [D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation](../../QuantumChannels/CoPRelativeQuantumnessRefutation.md)
