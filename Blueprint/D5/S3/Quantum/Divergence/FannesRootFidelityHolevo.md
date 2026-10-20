# The three-state root-fidelity Holevo bound

## Abstract

Root-fidelity matrix entropy bounds the Holevo quantity of every three-state ensemble.

**Definition 1.1 (Holevo quantity).**

$$\forall n \in \operatorname{Type},\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall p \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; \forall rho \in \operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \operatorname{holevo}\left(p, rho\right) = -(\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left((\sum_{i:\operatorname{Fin}\left(3\right)} ((p\left(i\right): \mathbb{C}) \cdot rho\left(i\right))) \cdot \operatorname{CFC.log}\left(\sum_{i:\operatorname{Fin}\left(3\right)} ((p\left(i\right): \mathbb{C}) \cdot rho\left(i\right))\right)\right)\right)) - \sum_{i:\operatorname{Fin}\left(3\right)} (p\left(i\right) \cdot -(\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left((rho\left(i\right)) \cdot \operatorname{CFC.log}\left(rho\left(i\right)\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Divergence/FannesRootFidelityHolevo.holevo` (`✓ std3`).

*Citation.* M. Fannes, F. de Melo, W. Roga, K. Życzkowski (2011). *Matrices of fidelities for ensembles of quantum states and the Holevo quantity*. URL: <https://arxiv.org/abs/1104.2271v1>.

*Commentary.*

Equation (2), page 3: χ(Eₖ) = S(ϱ) − ∑ᵢ pᵢ S(ϱᵢ), where ϱ = ∑ᵢ pᵢϱᵢ. Here the ensemble index is Fin 3.

**Definition 1.2 (Root-fidelity matrix).**

$$\forall n \in \operatorname{Type},\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall p \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; \forall rho \in \operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \forall i \in \operatorname{Fin}\left(3\right),\; \forall j \in \operatorname{Fin}\left(3\right),\; \operatorname{rootFidelityMatrix}\left(p, rho\right)\left(i, j\right) = ((\operatorname{Real.sqrt}\left(p\left(i\right) \cdot p\left(j\right)\right) \cdot \operatorname{FiniteTraceDistance.traceNorm}\left(\operatorname{CFC.sqrt}\left(rho\left(i\right)\right) \cdot \operatorname{CFC.sqrt}\left(rho\left(j\right)\right)\right): \mathbb{R}): \mathbb{C})$$

*Formalization.* `D5/S3/Quantum/Divergence/FannesRootFidelityHolevo.rootFidelityMatrix` (`✓ std3`).

*Citation.* M. Fannes, F. de Melo, W. Roga, K. Życzkowski (2011). *Matrices of fidelities for ensembles of quantum states and the Holevo quantity*. URL: <https://arxiv.org/abs/1104.2271v1>.

*Commentary.*

Equation (16), page 10: C√F(E₃) = [√(pᵢpⱼ)√Fᵢⱼ]ᵢⱼ. Each real matrix entry is embedded in the complex numbers.

**Definition 1.3 (Conjecture 1).**

$$claim \Leftrightarrow (\forall d \in \mathbb{N},\; \forall rho \in \operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall p \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; (\forall i \in \operatorname{Fin}\left(3\right),\; (\operatorname{Matrix.PosSemidef}\left(rho\left(i\right)\right)) \land (\operatorname{Matrix.trace}\left(rho\left(i\right)\right) = 1)) \Rightarrow ((\forall i \in \operatorname{Fin}\left(3\right),\; 0 \le p\left(i\right)) \Rightarrow ((\sum_{i:\operatorname{Fin}\left(3\right)} (p\left(i\right)) = 1) \Rightarrow (\operatorname{holevo}\left(p, rho\right) \le -(\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left((\operatorname{rootFidelityMatrix}\left(p, rho\right)) \cdot \operatorname{CFC.log}\left(\operatorname{rootFidelityMatrix}\left(p, rho\right)\right)\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/Divergence/FannesRootFidelityHolevo.claim` (`✓ std3`).

*Citation.* M. Fannes, F. de Melo, W. Roga, K. Życzkowski (2011). *Matrices of fidelities for ensembles of quantum states and the Holevo quantity*. URL: <https://arxiv.org/abs/1104.2271v1>.

*Commentary.*

Page 10, Conjecture 1: For any ensemble E₃ = {(pᵢ, ϱᵢ)} with K = 3 three states of arbitrary dimension d the corresponding Holevo quantity χ(E₃) is bounded from above by the entropy of the matrix C√F(E₃) defined in (16): χ(E₃) ≤ S(C√F(E₃)). A state is a positive semidefinite Matrix (Fin d) (Fin d) ℂ of trace one. The weights are nonnegative and sum to one. Every natural dimension is quantified; dimension zero has no such density matrix.

**Theorem 1.4 (The Holevo bound for three arbitrary states).**

$$\forall d \in \mathbb{N},\; \forall rho \in \operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall p \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; (\forall i \in \operatorname{Fin}\left(3\right),\; (\operatorname{Matrix.PosSemidef}\left(rho\left(i\right)\right)) \land (\operatorname{Matrix.trace}\left(rho\left(i\right)\right) = 1)) \Rightarrow ((\forall i \in \operatorname{Fin}\left(3\right),\; 0 \le p\left(i\right)) \Rightarrow ((\sum_{i:\operatorname{Fin}\left(3\right)} (p\left(i\right)) = 1) \Rightarrow (\operatorname{holevo}\left(p, rho\right) \le -(\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left((\operatorname{rootFidelityMatrix}\left(p, rho\right)) \cdot \operatorname{CFC.log}\left(\operatorname{rootFidelityMatrix}\left(p, rho\right)\right)\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/FannesRootFidelityHolevo.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Fannes, F. de Melo, W. Roga, K. Życzkowski (2011). *Matrices of fidelities for ensembles of quantum states and the Holevo quantity*. URL: <https://arxiv.org/abs/1104.2271v1>.

*Commentary.*

Two polar gauges make two cross products positive. An eigenbasis of the remaining polar unitary preserves all three root fidelities in one rank-one decomposition. Channel data processing bounds the Holevo quantity by its labelled rank-one refinement. The three-by-three entrywise-modulus entropy inequality and diagonal entropy accounting then bound that refinement by the entropy of the root-fidelity matrix. Singular states and zero weights require no limiting restriction.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/FannesRootFidelityHolevo.claim`
- Truth anchor: `D5/S3/Quantum/Divergence/FannesRootFidelityHolevo.holevo`
- Truth anchor: `D5/S3/Quantum/Divergence/FannesRootFidelityHolevo.result`
- Truth anchor: `D5/S3/Quantum/Divergence/FannesRootFidelityHolevo.rootFidelityMatrix`
- Dependency: [D5/S3/Quantum/Divergence/CanonicalChannelDPI](CanonicalChannelDPI.md)
- Dependency: [D5/S3/Quantum/Divergence/CanonicalRelativeModularModel](CanonicalRelativeModularModel.md)
- Dependency: [D5/S3/Quantum/Divergence/SupportAwareRelativeEntropy](SupportAwareRelativeEntropy.md)
- Dependency: [D5/S3/Quantum/Divergence/ThreeByThreeModulusEntropy](ThreeByThreeModulusEntropy.md)
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction](../Entanglement/ChoiKiemKye/ConstructionReduction.md)
- Dependency: [D5/S3/Quantum/Entanglement/UniversalReplacementCapacityGrowth](../Entanglement/UniversalReplacementCapacityGrowth.md)
- Dependency: [D5/S3/Quantum/FixedAlgebra/RecordFixedAlgebraDecomposition](../FixedAlgebra/RecordFixedAlgebraDecomposition.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Foundation/FiniteStateChannel.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/Information/ChenKatoBrandaoCMIRefutation](../Information/ChenKatoBrandaoCMIRefutation.md)
- Dependency: [D5/S3/Quantum/Information/NMLWMeasuredFidelitySeparation](../Information/NMLWMeasuredFidelitySeparation.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral](../Measurement/OccupationPartialTransposeSpectral.md)
- Dependency: [D5/S3/Quantum/Recovery/PurifiedLocalPath](../Recovery/PurifiedLocalPath.md)
- Dependency: [D5/S3/Quantum/Schatten/TraceNorm](../Schatten/TraceNorm.md)
- Dependency: [D5/S3/Quantum/Schatten/UnitarilyInvariantNorm](../Schatten/UnitarilyInvariantNorm.md)
- Dependency: [D5/S3/QuantumBounds/PeritoTensorBlockBound](../../QuantumBounds/PeritoTensorBlockBound.md)
