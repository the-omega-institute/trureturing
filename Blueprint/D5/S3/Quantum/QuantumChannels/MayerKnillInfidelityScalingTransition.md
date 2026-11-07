# Mayer–Knill infidelity transition

## Abstract

Scalar line-preserving matrices distinguish linear from square-root process infidelity for fixed connected spanning pure-input families.

**Definition 1.1 (unitInputFamily).**

$$\forall d \in \mathbb{N}, N \in \mathbb{N}, psi \in \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(d\right) \to \mathbb{C}\right),\; \operatorname{unitInputFamily}\left(psi\right) = \left(\forall k \in \operatorname{Fin}\left(N\right),\; \operatorname{dotProduct}\left(\operatorname{star}\left(psi\left(k\right)\right), psi\left(k\right)\right) = 1\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition.unitInputFamily` (`✓ std3`).

*Citation.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. DOI: [10.1103/PhysRevA.98.052326](https://doi.org/10.1103/PhysRevA.98.052326). URL: <https://arxiv.org/html/1805.04491v1>.

*Commentary.*

Mayer and Knill, arXiv:1805.04491v1, p. 2, §III: “Let {|ψₖ⟩}ₖ₌₁ᴺ be an indexed family of pure states in ℋ, fix ε=(ε₁,…,$\varepsilon_{N}$) with εₖ≥0, and let 𝒞(ε) be the convex set of CPTP maps ℰ such that for all k, ⟨ψₖ|ℰ(ψ̂ₖ)|ψₖ⟩ ≥ 1−εₖ. We refer to {|ψₖ⟩} as the set of input states. We wish to find $\left(F_{\mathrm{min}}\right)\left(\varepsilon\right)$=$\left(\min_{\mathcal{E} \in \mathcal{C}\left(\varepsilon\right)}\right)\left(F\left(\mathcal{E}\right)\right)$. Note that the minimum is achieved by compactness of the feasible set.” The coordinate vectors use Fin N and Fin d; the pure states are normalized.

**Definition 1.2 (spanInputFamily).**

$$\forall d \in \mathbb{N}, N \in \mathbb{N}, psi \in \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(d\right) \to \mathbb{C}\right),\; \operatorname{spanInputFamily}\left(psi\right) = \left(\operatorname{Submodule}.\operatorname{span}\left(\mathbb{C}, \operatorname{Set}.\operatorname{range}\left(psi\right)\right) = \operatorname{Top}.\operatorname{top}\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition.spanInputFamily` (`✓ std3`).

*Citation.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. DOI: [10.1103/PhysRevA.98.052326](https://doi.org/10.1103/PhysRevA.98.052326). URL: <https://arxiv.org/html/1805.04491v1>.

*Commentary.*

The complex span of the input vectors is the entire coordinate space. This is the spanning hypothesis in the source's unitary-identification criterion.

**Definition 1.3 (nonorthogonalityConnected).**

$$\forall d \in \mathbb{N}, N \in \mathbb{N}, psi \in \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(d\right) \to \mathbb{C}\right),\; \operatorname{nonorthogonalityConnected}\left(psi\right) = \left(\forall i \in \operatorname{Fin}\left(N\right), j \in \operatorname{Fin}\left(N\right),\; \operatorname{Relation}.\operatorname{EqvGen}\left(\operatorname{fun} a b \mapsto \neg (\operatorname{dotProduct}\left(\operatorname{star}\left(psi\left(a\right)\right), psi\left(b\right)\right) = 0), i, j\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition.nonorthogonalityConnected` (`✓ std3`).

*Citation.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. DOI: [10.1103/PhysRevA.98.052326](https://doi.org/10.1103/PhysRevA.98.052326). URL: <https://arxiv.org/html/1805.04491v1>.

*Commentary.*

Nonzero complex overlaps generate a single equivalence class. Paths may have any finite length, and indexed repeated inputs are allowed.

**Definition 1.4 (survivalFidelity).**

$$\forall d \in \mathbb{N}, Phi \in \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), psi \in \operatorname{Fin}\left(d\right) \to \mathbb{C},\; \operatorname{survivalFidelity}\left(Phi, psi\right) = \operatorname{Complex}.\operatorname{re}\left(\operatorname{dotProduct}\left(\operatorname{star}\left(psi\right), \operatorname{Matrix}.\operatorname{mulVec}\left(Phi\left(\operatorname{PureStateHandshake}.\operatorname{rankOneDensity}\left(psi\right)\right), psi\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition.survivalFidelity` (`✓ std3`).

*Citation.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. DOI: [10.1103/PhysRevA.98.052326](https://doi.org/10.1103/PhysRevA.98.052326). URL: <https://arxiv.org/html/1805.04491v1>.

*Commentary.*

The source's survival event is ⟨ψ∣E(ψ̂)∣ψ⟩. Here ψ̂ is the existing rankOneDensity, and the real part extracts the real-valued event probability for a CPTP map.

**Definition 1.5 (Choi matrix).**

$$\forall d \in \mathbb{N}, Phi \in \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{fun} (j: \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)) \mapsto \operatorname{fun} (k: \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)) \mapsto Phi\left(\operatorname{Matrix}.\operatorname{single}\left(j.2, k.2, 1\right)\right)\left(j.1, k.1\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/FiniteKrausRepresentation.choi_matrix` (`✓ std3`).

*Citation.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. DOI: [10.1103/PhysRevA.98.052326](https://doi.org/10.1103/PhysRevA.98.052326). URL: <https://arxiv.org/html/1805.04491v1>.

*Commentary.*

MatrixMap.choi_matrix is the matrix whose coordinates are obtained by applying Φ to Matrix.single j.2 k.2 1 and reading the j.1, k.1 entry.

**Definition 1.6 (f).**

$$\forall d \in \mathbb{N}, N \in \mathbb{N}, psi \in \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(d\right) \to \mathbb{C}\right), epsilon \in \mathbb{R},\; \operatorname{f}\left(psi, epsilon\right) = 1 - \operatorname{sInf}\left(\{ x : \mathbb{R} \mid \exists Phi \in \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{admissibleAt}\left(psi, epsilon, Phi\right) \land x = \frac{\operatorname{Complex}.\operatorname{re}\left(\operatorname{dotProduct}\left(\operatorname{star}\left(\operatorname{fun} (ij: \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)) \mapsto \operatorname{ite}\left(ij.1 = ij.2, \operatorname{Complex}.\operatorname{ofReal}\left(\operatorname{Real}.\operatorname{sqrt}\left(d\right)^{-1}\right), 0\right)\right), \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{fun} (j: \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)) \mapsto \operatorname{fun} (k: \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)) \mapsto Phi\left(\operatorname{Matrix}.\operatorname{single}\left(j.2, k.2, 1\right)\right)\left(j.1, k.1\right), \operatorname{fun} (ij: \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)) \mapsto \operatorname{ite}\left(ij.1 = ij.2, \operatorname{Complex}.\operatorname{ofReal}\left(\operatorname{Real}.\operatorname{sqrt}\left(d\right)^{-1}\right), 0\right)\right)\right)\right)}{d} \}\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition.f` (`✓ std3`).

*Citation.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. DOI: [10.1103/PhysRevA.98.052326](https://doi.org/10.1103/PhysRevA.98.052326). URL: <https://arxiv.org/html/1805.04491v1>.

*Commentary.*

The worst process infidelity is one minus the infimum of the normalized Choi overlap over admissible channels.

**Definition 1.7 (admissibleAt).**

$$\forall d \in \mathbb{N}, N \in \mathbb{N}, psi \in \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(d\right) \to \mathbb{C}\right), epsilon \in \mathbb{R}, Phi \in \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{admissibleAt}\left(psi, epsilon, Phi\right) = \left(\operatorname{ElementaryChannelDivisibility}.\operatorname{CPTP}\left(Phi\right) \land \left(\forall k \in \operatorname{Fin}\left(N\right),\; 1 - epsilon \le \operatorname{survivalFidelity}\left(Phi, psi\left(k\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition.admissibleAt` (`✓ std3`).

*Citation.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. DOI: [10.1103/PhysRevA.98.052326](https://doi.org/10.1103/PhysRevA.98.052326). URL: <https://arxiv.org/html/1805.04491v1>.

*Commentary.*

Mayer and Knill, arXiv:1805.04491v1, p. 2, §III: “Let {|ψₖ⟩}ₖ₌₁ᴺ be an indexed family of pure states in ℋ, fix ε=(ε₁,…,$\varepsilon_{N}$) with εₖ≥0, and let 𝒞(ε) be the convex set of CPTP maps ℰ such that for all k, ⟨ψₖ|ℰ(ψ̂ₖ)|ψₖ⟩ ≥ 1−εₖ. We refer to {|ψₖ⟩} as the set of input states. We wish to find $\left(F_{\mathrm{min}}\right)\left(\varepsilon\right)$=$\left(\min_{\mathcal{E} \in \mathcal{C}\left(\varepsilon\right)}\right)\left(F\left(\mathcal{E}\right)\right)$. Note that the minimum is achieved by compactness of the feasible set.” The error vector is constant, with every coordinate equal to epsilon.

**Definition 1.8 (obstructionSpace).**

$$\forall d \in \mathbb{N}, N \in \mathbb{N}, psi \in \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(d\right) \to \mathbb{C}\right),\; \operatorname{obstructionSpace}\left(psi\right) = \{ A : \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right) \mid \forall k \in \operatorname{Fin}\left(N\right),\; \operatorname{Matrix}.\operatorname{mulVec}\left(1 - \operatorname{PureStateHandshake}.\operatorname{rankOneDensity}\left(psi\left(k\right)\right), \operatorname{Matrix}.\operatorname{mulVec}\left(A, psi\left(k\right)\right)\right) = 0 \}$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition.obstructionSpace` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. DOI: [10.1103/PhysRevA.98.052326](https://doi.org/10.1103/PhysRevA.98.052326). URL: <https://arxiv.org/html/1805.04491v1>.

*Commentary.*

For unit input families, a matrix belongs to the obstruction space exactly when it preserves each tested line. The orthogonal residual after applying that matrix vanishes at every input.

**Definition 1.9 (scalarObstruction).**

$$\forall d \in \mathbb{N}, N \in \mathbb{N}, psi \in \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(d\right) \to \mathbb{C}\right),\; \operatorname{scalarObstruction}\left(psi\right) = \left(\forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; A \in \operatorname{obstructionSpace}\left(psi\right) \Rightarrow \left(\exists z \in \mathbb{C},\; A = \operatorname{HSMul}.\operatorname{hSMul}\left(z, 1 : \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition.scalarObstruction` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. DOI: [10.1103/PhysRevA.98.052326](https://doi.org/10.1103/PhysRevA.98.052326). URL: <https://arxiv.org/html/1805.04491v1>.

*Commentary.*

Every line-preserving matrix is a scalar identity. Unit inputs ensure that every scalar identity does preserve all the tested lines.

**Definition 1.10 (LinearScaling).**

$$\forall d \in \mathbb{N}, N \in \mathbb{N}, psi \in \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(d\right) \to \mathbb{C}\right),\; \operatorname{LinearScaling}\left(psi\right) = \left(\exists c \in \mathbb{R}, C \in \mathbb{R}, delta \in \mathbb{R},\; 0 < c \land \left(0 < C \land \left(0 < delta \land \left(\forall epsilon \in \mathbb{R},\; 0 < epsilon \Rightarrow \left(epsilon < delta \Rightarrow \left(c \cdot epsilon \le \operatorname{f}\left(psi, epsilon\right) \land \operatorname{f}\left(psi, epsilon\right) \le C \cdot epsilon\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition.LinearScaling` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. DOI: [10.1103/PhysRevA.98.052326](https://doi.org/10.1103/PhysRevA.98.052326). URL: <https://arxiv.org/html/1805.04491v1>.

*Commentary.*

There are positive lower and upper constants and a positive radius on which the infidelity lies between the corresponding multiples of epsilon. Constants are chosen separately for each fixed input family.

**Definition 1.11 (SqrtScaling).**

$$\forall d \in \mathbb{N}, N \in \mathbb{N}, psi \in \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(d\right) \to \mathbb{C}\right),\; \operatorname{SqrtScaling}\left(psi\right) = \left(\exists c \in \mathbb{R}, C \in \mathbb{R}, delta \in \mathbb{R},\; 0 < c \land \left(0 < C \land \left(0 < delta \land \left(\forall epsilon \in \mathbb{R},\; 0 < epsilon \Rightarrow \left(epsilon < delta \Rightarrow \left(c \cdot \operatorname{Real}.\operatorname{sqrt}\left(epsilon\right) \le \operatorname{f}\left(psi, epsilon\right) \land \operatorname{f}\left(psi, epsilon\right) \le C \cdot \operatorname{Real}.\operatorname{sqrt}\left(epsilon\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition.SqrtScaling` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. DOI: [10.1103/PhysRevA.98.052326](https://doi.org/10.1103/PhysRevA.98.052326). URL: <https://arxiv.org/html/1805.04491v1>.

*Commentary.*

The same two-sided local estimate holds with Real.sqrt epsilon. The quantified errors are strictly positive and smaller than the radius.

**Definition 1.12 (claim).**

$$claim = \left(\forall d \in \mathbb{N}, N \in \mathbb{N}, psi \in \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(d\right) \to \mathbb{C}\right),\; 2 \le d \Rightarrow \left(\operatorname{unitInputFamily}\left(psi\right) \Rightarrow \left(\operatorname{spanInputFamily}\left(psi\right) \Rightarrow \left(\operatorname{nonorthogonalityConnected}\left(psi\right) \Rightarrow \left(((\operatorname{scalarObstruction}\left(psi\right)) \Leftrightarrow (\operatorname{LinearScaling}\left(psi\right))) \land ((\neg (\operatorname{scalarObstruction}\left(psi\right))) \Leftrightarrow (\operatorname{SqrtScaling}\left(psi\right)))\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. DOI: [10.1103/PhysRevA.98.052326](https://doi.org/10.1103/PhysRevA.98.052326). URL: <https://arxiv.org/html/1805.04491v1>.

*Commentary.*

Mayer and Knill, arXiv:1805.04491v1, p. 4: “First, note that the lowest order term in the lower bound is of order √ε. This scaling behavior matches our empirical observations from numerically solving the SDP given by Eq. (5). However, we find that for many sets of input states containing more than d states, the O(√ε) term vanishes and the process infidelity becomes linear in ε for small error. Examples include the basis states plus the totally rotated state, as well as the symmetric POVM states defined in the next section. The transition from sub-linear to linear scaling is not explained by the proof of Thm. 2 and thus remains an open question.” The proposition quantifies over all finite unit spanning input families in dimensions at least two whose nonorthogonality graph is connected. It characterizes the two possible rates by the line-preserving obstruction space.

**Theorem 1.13 (result).**

$$\forall d \in \mathbb{N}, N \in \mathbb{N}, psi \in \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(d\right) \to \mathbb{C}\right),\; 2 \le d \Rightarrow \left(\operatorname{unitInputFamily}\left(psi\right) \Rightarrow \left(\operatorname{spanInputFamily}\left(psi\right) \Rightarrow \left(\operatorname{nonorthogonalityConnected}\left(psi\right) \Rightarrow \left(((\operatorname{scalarObstruction}\left(psi\right)) \Leftrightarrow (\operatorname{LinearScaling}\left(psi\right))) \land ((\neg (\operatorname{scalarObstruction}\left(psi\right))) \Leftrightarrow (\operatorname{SqrtScaling}\left(psi\right)))\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition.result` (`✓ std3`). ∎

*Resolves.* `Problems/mayer-knill-infidelity-scaling` (proved) by `D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mayer-knill-infidelity-scaling","declaration_gid":"D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. DOI: [10.1103/PhysRevA.98.052326](https://doi.org/10.1103/PhysRevA.98.052326). URL: <https://arxiv.org/html/1805.04491v1>.

*Commentary.*

The traceless Kraus squared norms sum to d times process infidelity, and the tested orthogonal residual squared norms sum to each input error. Scalar obstruction makes the finite-dimensional detection map injective, giving the linear upper estimate; an identity/reset mixture supplies a positive linear lower estimate. A traceless nonscalar obstruction admits a positive square-root Kraus completion and produces a square-root lower estimate. Stinespring overlap defects propagate along the finite connected graph, and spanning evaluation controls the whole matrix, giving the matching square-root upper estimate. The two local rates cannot both hold. Constants may depend on the spanning condition and the nonzero overlaps; no uniform estimate for degenerating families is asserted.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/FiniteKrausRepresentation.choi_matrix`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition.LinearScaling`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition.SqrtScaling`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition.admissibleAt`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition.f`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition.nonorthogonalityConnected`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition.obstructionSpace`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition.result`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition.scalarObstruction`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition.spanInputFamily`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition.survivalFidelity`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition.unitInputFamily`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../Foundation/FiniteKrausRepresentation.md)
- Dependency: [D5/S3/Quantum/GNSMatrix](../GNSMatrix.md)
- Dependency: [D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral](../Measurement/OccupationPartialTransposeSpectral.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../PureState/PureStateHandshake.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility](ElementaryChannelDivisibility.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingCore](MayerKnillInfidelityScalingCore.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/SparseProbeCoercivity](SparseProbeCoercivity.md)
- Dependency: [D5/S3/Quantum/Recovery/ActualChannelAlgebra](../Recovery/ActualChannelAlgebra.md)
- Dependency: [D5/S3/Quantum/Recovery/KrausCompletion](../Recovery/KrausCompletion.md)
- Dependency: [D5/S3/Quantum/Reduction/ProbeComponentRigidity](../Reduction/ProbeComponentRigidity.md)
- Dependency: [D5/S3/QuantumBounds/PeritoTsirelson](../../QuantumBounds/PeritoTsirelson.md)
