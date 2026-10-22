# Purify-and-clone is not optimal for one-site worst-case risk

## Abstract

A symmetric quantum channel has one-site worst-case infidelity at most one sixth, while purify-and-clone has risk at least one fifth in system and environment dimension two.

**Definition 1.1 (sqFidelity).**

$$\forall a \in \operatorname{Type},\; [\operatorname{Fintype}\left(a\right)] [\operatorname{DecidableEq}\left(a\right)], \forall alpha \in \operatorname{Matrix}\left(a, a, \mathbb{C}\right),\; \forall beta \in \operatorname{Matrix}\left(a, a, \mathbb{C}\right),\; \operatorname{sqFidelity}\left(alpha, beta\right) = \operatorname{Complex}.\operatorname{re}\left(\operatorname{Matrix}.\operatorname{trace}\left(\operatorname{CFC}.\operatorname{sqrt}\left(((\operatorname{CFC}.\operatorname{sqrt}\left(alpha\right)) \cdot (beta)) \cdot (\operatorname{CFC}.\operatorname{sqrt}\left(alpha\right))\right)\right)\right)^{2}$$

*Formalization.* `D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation.sqFidelity` (`✓ std3`).

*Citation.* Z. Li; E. Theil; A. W. Harrow; I. Chuang (2026). *An Exponential Sample-Complexity Advantage for Coherent Quantum Inference*. DOI: [10.48550/arXiv.2605.21457](https://doi.org/10.48550/arXiv.2605.21457). URL: <https://arxiv.org/abs/2605.21457v2>.

*Commentary.*

Squared Uhlmann fidelity is (Tr √(√α β √α))². The formula uses the real part of the trace of the positive square root.

**Definition 1.2 (purifications).**

$$\forall d \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall rho \in \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right),\; \operatorname{purifications}\left(r, rho\right) = \{ Psi : \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right)), \mathbb{C}\right) \mid ((Psi \in \operatorname{Set}.\operatorname{range}\left(\operatorname{fun} (sigma : \operatorname{DensityState}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right))\right)) \mapsto \operatorname{CStarMatrix}.\operatorname{ofMatrix}.\operatorname{symm}\left(\operatorname{val}\left(sigma\right)\right)\right)) \land ((\operatorname{Matrix}.\operatorname{rank}\left(Psi\right) = 1) \land (\operatorname{partialTraceRight}\left(Psi\right) = \operatorname{CStarMatrix}.\operatorname{ofMatrix}.\operatorname{symm}\left(\operatorname{val}\left(rho\right)\right)))) \}$$

*Formalization.* `D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation.purifications` (`✓ std3`).

*Citation.* Z. Li; E. Theil; A. W. Harrow; I. Chuang (2026). *An Exponential Sample-Complexity Advantage for Coherent Quantum Inference*. DOI: [10.48550/arXiv.2605.21457](https://doi.org/10.48550/arXiv.2605.21457). URL: <https://arxiv.org/abs/2605.21457v2>.

*Commentary.*

Section S3 A, p. 8: “That is, C(ρ) is the convex hull of all m-tensor powers of purifications of ρ.” Here purifications r rho is the set of trace-one positive rank-one matrices whose environment partial trace is rho. The range of the conversion from DensityState is exactly the set of ordinary density matrices.

**Definition 1.3 (oneSiteMarginal).**

$$\forall d \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall Xi \in \operatorname{Matrix}\left(((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right)) \times (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right))), ((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right)) \times (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right))), \mathbb{C}\right),\; \forall i \in \operatorname{Fin}\left(2\right),\; \operatorname{oneSiteMarginal}\left(Xi, i\right) = \operatorname{if} (i = 0) \operatorname{then} \operatorname{partialTraceRight}\left(Xi\right) \operatorname{else} \operatorname{partialTraceLeft}\left(Xi\right)$$

*Formalization.* `D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation.oneSiteMarginal` (`✓ std3`).

*Citation.* Z. Li; E. Theil; A. W. Harrow; I. Chuang (2026). *An Exponential Sample-Complexity Advantage for Coherent Quantum Inference*. DOI: [10.48550/arXiv.2605.21457](https://doi.org/10.48550/arXiv.2605.21457). URL: <https://arxiv.org/abs/2605.21457v2>.

*Commentary.*

The two choices retain the first and second joint system-environment sites. The environment inside a retained site is not discarded.

**Definition 1.4 (oneSiteLoss).**

$$\forall d \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall rho \in \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right),\; \forall Xi \in \operatorname{Matrix}\left(((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right)) \times (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right))), ((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right)) \times (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right))), \mathbb{C}\right),\; \operatorname{oneSiteLoss}\left(rho, Xi\right) = \operatorname{sInf}\left(\operatorname{Set}.\operatorname{image}\left(\operatorname{fun} (gamma : \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right)), \mathbb{C}\right)) \mapsto ((\operatorname{max}\left(1 - \operatorname{sqFidelity}\left(gamma, \operatorname{oneSiteMarginal}\left(Xi, 0\right)\right), 1 - \operatorname{sqFidelity}\left(gamma, \operatorname{oneSiteMarginal}\left(Xi, 1\right)\right)\right) : \mathbb{R}) : \operatorname{EReal}), \operatorname{convexHull}\left(\mathbb{R}, \operatorname{purifications}\left(r, rho\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation.oneSiteLoss` (`✓ std3`).

*Citation.* Z. Li; E. Theil; A. W. Harrow; I. Chuang (2026). *An Exponential Sample-Complexity Advantage for Coherent Quantum Inference*. DOI: [10.48550/arXiv.2605.21457](https://doi.org/10.48550/arXiv.2605.21457). URL: <https://arxiv.org/abs/2605.21457v2>.

*Commentary.*

Equation (S13), p. 5, takes the infimum over one common gamma in conv(c(Sigma)) before the maximum over the sites. For two sites the maximum has two entries. The real infidelities are embedded into EReal before taking the infimum.

**Definition 1.5 (worstCaseOneSiteRisk).**

$$\forall d \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall T \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right) \to \operatorname{Matrix}\left(((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right)) \times (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right))), ((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right)) \times (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right))), \mathbb{C}\right),\; \operatorname{worstCaseOneSiteRisk}\left(T\right) = \operatorname{sSup}\left(\{ x : \operatorname{EReal} \mid (\exists rho \in \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right),\; (\operatorname{Matrix}.\operatorname{rank}\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}.\operatorname{symm}\left(\operatorname{val}\left(rho\right)\right)\right) \le r) \land (x = \operatorname{oneSiteLoss}\left(rho, T\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}.\operatorname{symm}\left(\operatorname{val}\left(rho\right)\right)\right)\right))) \}\right)$$

*Formalization.* `D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation.worstCaseOneSiteRisk` (`✓ std3`).

*Citation.* Z. Li; E. Theil; A. W. Harrow; I. Chuang (2026). *An Exponential Sample-Complexity Advantage for Coherent Quantum Inference*. DOI: [10.48550/arXiv.2605.21457](https://doi.org/10.48550/arXiv.2605.21457). URL: <https://arxiv.org/abs/2605.21457v2>.

*Commentary.*

Equation (7) specializes to the supremum of the one-site losses over every density matrix of rank at most r. The risk is defined for arbitrary matrix maps; the optimality statement restricts the competitors to QuantumChannel.

**Definition 1.6 (TotallySymmetricSupport).**

$$\forall a \in \operatorname{Type},\; [\operatorname{Fintype}\left(a\right)] [\operatorname{DecidableEq}\left(a\right)], \forall Xi \in \operatorname{Matrix}\left((a \times a), (a \times a), \mathbb{C}\right),\; (\operatorname{TotallySymmetricSupport}\left(Xi\right)) \Leftrightarrow ((((\frac{1}{2}) \cdot (1 + \operatorname{Equiv}.\operatorname{Perm}.\operatorname{permMatrix}\left(\mathbb{C}, \operatorname{Equiv}.\operatorname{prodComm}\left(a, a\right)\right))) \cdot (Xi)) \cdot ((\frac{1}{2}) \cdot (1 + \operatorname{Equiv}.\operatorname{Perm}.\operatorname{permMatrix}\left(\mathbb{C}, \operatorname{Equiv}.\operatorname{prodComm}\left(a, a\right)\right))) = Xi)$$

*Formalization.* `D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation.TotallySymmetricSupport` (`✓ std3`).

*Citation.* Z. Li; E. Theil; A. W. Harrow; I. Chuang (2026). *An Exponential Sample-Complexity Advantage for Coherent Quantum Inference*. DOI: [10.48550/arXiv.2605.21457](https://doi.org/10.48550/arXiv.2605.21457). URL: <https://arxiv.org/abs/2605.21457v2>.

*Commentary.*

The output lies in the symmetric subspace on both sides: S Xi S = Xi. Invariance under conjugation by the swap alone is insufficient.

**Definition 1.7 (wernerOneToTwo).**

$$\forall a \in \operatorname{Type},\; [\operatorname{Fintype}\left(a\right)] [\operatorname{DecidableEq}\left(a\right)], \forall X \in \operatorname{Matrix}\left(a, a, \mathbb{C}\right),\; \operatorname{wernerOneToTwo}\left(X\right) = (\frac{2}{(\operatorname{Fintype}.\operatorname{card}\left(a\right) : \mathbb{C}) + 1}) \cdot ((((\frac{1}{2}) \cdot (1 + \operatorname{Equiv}.\operatorname{Perm}.\operatorname{permMatrix}\left(\mathbb{C}, \operatorname{Equiv}.\operatorname{prodComm}\left(a, a\right)\right))) \cdot (\operatorname{Matrix}.\operatorname{kronecker}\left(X, 1\right))) \cdot ((\frac{1}{2}) \cdot (1 + \operatorname{Equiv}.\operatorname{Perm}.\operatorname{permMatrix}\left(\mathbb{C}, \operatorname{Equiv}.\operatorname{prodComm}\left(a, a\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation.wernerOneToTwo` (`✓ std3`).

*Citation.* Z. Li; E. Theil; A. W. Harrow; I. Chuang (2026). *An Exponential Sample-Complexity Advantage for Coherent Quantum Inference*. DOI: [10.48550/arXiv.2605.21457](https://doi.org/10.48550/arXiv.2605.21457). URL: <https://arxiv.org/abs/2605.21457v2>.

*Commentary.*

The one-to-two pure-state cloning channel in equation (S35) has coefficient 2/(D+1), with D equal to the cardinality of the input index type.

**Definition 1.8 (randomPurifyOne).**

$$\forall d \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{randomPurifyOne}\left(r, X\right) = \operatorname{Matrix}.\operatorname{kronecker}\left(X, ((r : \mathbb{C})^{-1}) \cdot (1)\right)$$

*Formalization.* `D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation.randomPurifyOne` (`✓ std3`).

*Citation.* Z. Li; E. Theil; A. W. Harrow; I. Chuang (2026). *An Exponential Sample-Complexity Advantage for Coherent Quantum Inference*. DOI: [10.48550/arXiv.2605.21457](https://doi.org/10.48550/arXiv.2605.21457). URL: <https://arxiv.org/abs/2605.21457v2>.

*Commentary.*

Equations (S37c) and (S38), p. 9, specialize at one input to rho tensor I/r, obtained by averaging the environment of a purification.

**Definition 1.9 (purifyAndClone).**

$$\forall d \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{purifyAndClone}\left(d, r, X\right) = \operatorname{wernerOneToTwo}\left(\operatorname{randomPurifyOne}\left(r, X\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation.purifyAndClone` (`✓ std3`).

*Citation.* Z. Li; E. Theil; A. W. Harrow; I. Chuang (2026). *An Exponential Sample-Complexity Advantage for Coherent Quantum Inference*. DOI: [10.48550/arXiv.2605.21457](https://doi.org/10.48550/arXiv.2605.21457). URL: <https://arxiv.org/abs/2605.21457v2>.

*Commentary.*

Equation (S35) at n = 1 and m = 2 first applies randomPurifyOne, then the Werner cloner in dimension d r.

**Definition 1.10 (AdmissibleChannel).**

$$\forall d \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall Phi \in \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), ((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right)) \times (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right)))\right),\; (\operatorname{AdmissibleChannel}\left(Phi\right)) \Leftrightarrow (\forall rho \in \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right),\; (\operatorname{Matrix}.\operatorname{rank}\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}.\operatorname{symm}\left(\operatorname{val}\left(rho\right)\right)\right) \le r) \Rightarrow (\operatorname{TotallySymmetricSupport}\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}.\operatorname{symm}\left(\operatorname{QuantumChannel}.\operatorname{toCompletelyPositiveMap}\left(Phi, \operatorname{CStarMatrix}.\operatorname{ofMatrix}\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}.\operatorname{symm}\left(\operatorname{val}\left(rho\right)\right)\right)\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation.AdmissibleChannel` (`✓ std3`).

*Citation.* Z. Li; E. Theil; A. W. Harrow; I. Chuang (2026). *An Exponential Sample-Complexity Advantage for Coherent Quantum Inference*. DOI: [10.48550/arXiv.2605.21457](https://doi.org/10.48550/arXiv.2605.21457). URL: <https://arxiv.org/abs/2605.21457v2>.

*Commentary.*

Section S3 A, p. 8 restricts the output to the totally symmetric subspace of the joint system and environment sites. This restriction holds for every density input of rank at most r.

**Definition 1.11 (claim).**

$$(\operatorname{claim}) \Leftrightarrow (\forall d \in \mathbb{N},\; \forall r \in \mathbb{N},\; (1 \le r) \Rightarrow ((r \le d) \Rightarrow (\forall Phi \in \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), ((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right)) \times (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right)))\right),\; (\operatorname{AdmissibleChannel}\left(Phi\right)) \Rightarrow (\operatorname{worstCaseOneSiteRisk}\left(\operatorname{purifyAndClone}\left(d, r\right)\right) \le \operatorname{worstCaseOneSiteRisk}\left(\operatorname{fun} (X : \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)) \mapsto \operatorname{CStarMatrix}.\operatorname{ofMatrix}.\operatorname{symm}\left(\operatorname{QuantumChannel}.\operatorname{toCompletelyPositiveMap}\left(Phi, \operatorname{CStarMatrix}.\operatorname{ofMatrix}\left(X\right)\right)\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation.claim` (`✓ std3`).

*Citation.* Z. Li; E. Theil; A. W. Harrow; I. Chuang (2026). *An Exponential Sample-Complexity Advantage for Coherent Quantum Inference*. DOI: [10.48550/arXiv.2605.21457](https://doi.org/10.48550/arXiv.2605.21457). URL: <https://arxiv.org/abs/2605.21457v2>.

*Commentary.*

Section S3 A, p. 9: “This channel is optimal for m ≤ n (see Ref. [S2]), and we conjecture that it is also optimal for m > n.” The formula takes n = 1 and m = 2 and the worst-case one-site infidelity interpretation. Both system and environment registers belong to each site. The dimensions satisfy 1 ≤ r ≤ d, and all input states of rank at most r occur.

**Theorem 1.12 (result).**

$$\neg (\forall d \in \mathbb{N},\; \forall r \in \mathbb{N},\; (1 \le r) \Rightarrow ((r \le d) \Rightarrow (\forall Phi \in \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), ((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right)) \times (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(r\right)))\right),\; (\operatorname{AdmissibleChannel}\left(Phi\right)) \Rightarrow (\operatorname{worstCaseOneSiteRisk}\left(\operatorname{purifyAndClone}\left(d, r\right)\right) \le \operatorname{worstCaseOneSiteRisk}\left(\operatorname{fun} (X : \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)) \mapsto \operatorname{CStarMatrix}.\operatorname{ofMatrix}.\operatorname{symm}\left(\operatorname{QuantumChannel}.\operatorname{toCompletelyPositiveMap}\left(Phi, \operatorname{CStarMatrix}.\operatorname{ofMatrix}\left(X\right)\right)\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Z. Li; E. Theil; A. W. Harrow; I. Chuang (2026). *An Exponential Sample-Complexity Advantage for Coherent Quantum Inference*. DOI: [10.48550/arXiv.2605.21457](https://doi.org/10.48550/arXiv.2605.21457). URL: <https://arxiv.org/abs/2605.21457v2>.

*Commentary.*

In dimension d = r = 2, clone the system with the two-dimensional Werner cloner and tensor its output with one third of the symmetric environment projector, then reorder the registers into two sites. Its Kraus operators give a completely positive trace-preserving channel. Both-sided symmetric support holds. A four-element Pauli average puts rho tensor I/2 in the common target convex hull for every input. Matrix square-root order gives fidelity at least 5/6 for this channel. For the pure zero input, every target has fidelity at most 4/5 with the purify-and-clone marginal. Thus the respective worst-case risks are at most 1/6 and at least 1/5. The universal inequality fails. The all-site and average risks and a strict-improvement family in arbitrary dimensions are not asserted.

## References

- Truth anchor: `D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation.AdmissibleChannel`
- Truth anchor: `D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation.TotallySymmetricSupport`
- Truth anchor: `D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation.oneSiteLoss`
- Truth anchor: `D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation.oneSiteMarginal`
- Truth anchor: `D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation.purifications`
- Truth anchor: `D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation.purifyAndClone`
- Truth anchor: `D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation.randomPurifyOne`
- Truth anchor: `D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation.result`
- Truth anchor: `D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation.sqFidelity`
- Truth anchor: `D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation.wernerOneToTwo`
- Truth anchor: `D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation.worstCaseOneSiteRisk`
- Dependency: [D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics](../Decoherence/ProjectedUnistochasticDynamics.md)
- Dependency: [D5/S3/Quantum/FiniteDimensional](../FiniteDimensional.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Foundation/FiniteStateChannel.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation](../Measurements/BroadcastingChannelExtremaRefutation.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../PureState/PureStateHandshake.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings](../QuantumChannels/QubitWassersteinCouplings.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/WassersteinComplexityNonconvex](../QuantumChannels/WassersteinComplexityNonconvex.md)
- Dependency: [D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl](../RandomCircuits/HaarTwoCopyTwirl.md)
- Dependency: [D5/S3/Quantum/Subentropy/Basic](../Subentropy/Basic.md)
- Dependency: [D5/S3/Quantum/Subentropy/PinchingGap](../Subentropy/PinchingGap.md)
- Dependency: [D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation](../../QuantumChannels/CoPRelativeQuantumnessRefutation.md)
- Dependency: [D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation](../../QuantumChannels/PassiveMemoryNonclassicalRefutation.md)
