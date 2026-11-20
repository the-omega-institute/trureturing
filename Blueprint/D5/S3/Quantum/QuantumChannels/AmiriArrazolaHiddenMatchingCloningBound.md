# The hidden-matching cloning bound

## Abstract

Hidden-matching cloning has mean marginal fidelity at most one half plus 1/n.

The input dimension is n, and the two output factors both have dimension n. A bit string is a function from Fin n to Fin 2. The coordinates 0 through n − 1 relabel the source's coordinates 1 through n. QuantumChannel is the complex completely positive trace-preserving linear-map carrier. The output coordinates are ordered Y × Z; partialTraceRight traces out Z and partialTraceLeft traces out Y. All inverses and divisions in these formulas are scalar operations. The theorem requires n ≥ 2, so sqrt n and n are nonzero.

**Definition 1.1 (The hidden-matching vector).**

$$\forall (n: \mathbb{N}), (\forall (x: (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right))), (\operatorname{phi}\left(n, x\right) = (\lambda (i: \operatorname{Fin}\left(n\right)), (((\operatorname{Real}.\operatorname{sqrt}\left((n: \mathbb{R})\right): \mathbb{C}))^{-1} \cdot ((-1: \mathbb{C}))^{\operatorname{Fin}.\operatorname{val}\left(x\left(i\right)\right)}))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/AmiriArrazolaHiddenMatchingCloningBound.phi` (`✓ std3`).

*Citation.* Ryan Amiri and Juan Miguel Arrazola (2016). *Quantum money with nearly optimal error tolerance*. DOI: [10.1103/PhysRevA.95.062334](https://doi.org/10.1103/PhysRevA.95.062334). URL: <https://arxiv.org/abs/1610.06345v1>.

*Commentary.*

Equation (4), p. 3: “In hidden matching QRGs the set of possible inputs is the set of all n-bit strings, each chosen with equal probability, where n is an even number. Alice encodes her input into the n-dimensional pure state” followed by |φ_x⟩ = (1/√n) ∑ᵢ₌₁ⁿ (−1)^{x_i}|i⟩. The displayed coordinate function is this vector in the computational basis.

**Definition 1.2 (The pure input matrix).**

$$\forall (n: \mathbb{N}), (\forall (x: (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right))), (\operatorname{rho}\left(n, x\right) = \operatorname{CStarMatrix}.\operatorname{ofMatrix}\left(\operatorname{Matrix}.\operatorname{vecMulVec}\left(\operatorname{phi}\left(n, x\right), \operatorname{star}\left(\operatorname{phi}\left(n, x\right)\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/AmiriArrazolaHiddenMatchingCloningBound.rho` (`✓ std3`).

*Citation.* Ryan Amiri and Juan Miguel Arrazola (2016). *Quantum money with nearly optimal error tolerance*. DOI: [10.1103/PhysRevA.95.062334](https://doi.org/10.1103/PhysRevA.95.062334). URL: <https://arxiv.org/abs/1610.06345v1>.

*Commentary.*

Section II A 2, p. 6: “In reference to Fig. 4, we refer to these states as the white states, and start by considering a single such state, φ_{xⁱ} := |φ_{xⁱ}⟩⟨φ_{xⁱ}|, contained in the coin.” “For simplicity, we drop the superscript on the n-bit strings xⁱ in all that follows.” Matrix.vecMulVec forms that outer product, and CStarMatrix.ofMatrix places the matrix in the channel's ordered matrix carrier.

**Definition 1.3 (The first marginal).**

$$\forall (n: \mathbb{N}), (\forall (N: \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(n\right), (\operatorname{Fin}\left(n\right)\times\operatorname{Fin}\left(n\right))\right)), (\forall (x: (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right))), (\operatorname{eta}\left(n, N, x\right) = \operatorname{partialTraceRight}\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}.\operatorname{symm}\left(N.\operatorname{toCompletelyPositiveMap}\left(\operatorname{rho}\left(n, x\right)\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/AmiriArrazolaHiddenMatchingCloningBound.eta` (`✓ std3`).

*Citation.* Ryan Amiri and Juan Miguel Arrazola (2016). *Quantum money with nearly optimal error tolerance*. DOI: [10.1103/PhysRevA.95.062334](https://doi.org/10.1103/PhysRevA.95.062334). URL: <https://arxiv.org/abs/1610.06345v1>.

*Commentary.*

Equation (11), p. 7: “where η_x = Tr_Z[Ψ(|φ_x⟩⟨φ_x|)] and τ_x = Tr_Y[Ψ(|φ_x⟩⟨φ_x|)].” The first expression traces out the second output factor.

**Definition 1.4 (The second marginal).**

$$\forall (n: \mathbb{N}), (\forall (N: \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(n\right), (\operatorname{Fin}\left(n\right)\times\operatorname{Fin}\left(n\right))\right)), (\forall (x: (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right))), (\operatorname{tau}\left(n, N, x\right) = \operatorname{partialTraceLeft}\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}.\operatorname{symm}\left(N.\operatorname{toCompletelyPositiveMap}\left(\operatorname{rho}\left(n, x\right)\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/AmiriArrazolaHiddenMatchingCloningBound.tau` (`✓ std3`).

*Citation.* Ryan Amiri and Juan Miguel Arrazola (2016). *Quantum money with nearly optimal error tolerance*. DOI: [10.1103/PhysRevA.95.062334](https://doi.org/10.1103/PhysRevA.95.062334). URL: <https://arxiv.org/abs/1610.06345v1>.

*Commentary.*

Equation (11), p. 7: “where η_x = Tr_Z[Ψ(|φ_x⟩⟨φ_x|)] and τ_x = Tr_Y[Ψ(|φ_x⟩⟨φ_x|)].” The second expression traces out the first output factor.

**Definition 1.5 (The mean marginal fidelity).**

$$\forall (n: \mathbb{N}), (\forall (N: \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(n\right), (\operatorname{Fin}\left(n\right)\times\operatorname{Fin}\left(n\right))\right)), (\operatorname{meanFidelity}\left(n, N\right) = \frac{1}{((2: \mathbb{R}))^{n}} \cdot \sum_{(x: (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right)))} (\frac{\operatorname{Complex}.\operatorname{re}\left(\operatorname{dotProduct}\left(\operatorname{star}\left(\operatorname{phi}\left(n, x\right)\right), \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{eta}\left(n, N, x\right), \operatorname{phi}\left(n, x\right)\right)\right)\right) + \operatorname{Complex}.\operatorname{re}\left(\operatorname{dotProduct}\left(\operatorname{star}\left(\operatorname{phi}\left(n, x\right)\right), \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{tau}\left(n, N, x\right), \operatorname{phi}\left(n, x\right)\right)\right)\right)}{2})))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/AmiriArrazolaHiddenMatchingCloningBound.meanFidelity` (`✓ std3`).

*Citation.* Ryan Amiri and Juan Miguel Arrazola (2016). *Quantum money with nearly optimal error tolerance*. DOI: [10.1103/PhysRevA.95.062334](https://doi.org/10.1103/PhysRevA.95.062334). URL: <https://arxiv.org/abs/1610.06345v1>.

*Commentary.*

Equation (11), p. 7: “We want to find the channel that maximises” F̄ = 2⁻ⁿ ∑ₓ (⟨φ_x|η_x|φ_x⟩ + ⟨φ_x|τ_x|φ_x⟩)/2. The sum ranges over all functions Fin n → Fin 2, exactly 2ⁿ inputs. Complex.re gives the real scalar order on the two expectations.

**Definition 1.6 (The dimension-uniform assertion).**

$$\operatorname{claim} = \forall (n: \mathbb{N}), ((2 \le n) \Rightarrow ((\operatorname{Even}\left(n\right)) \Rightarrow (\forall (N: \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(n\right), (\operatorname{Fin}\left(n\right)\times\operatorname{Fin}\left(n\right))\right)), (\operatorname{meanFidelity}\left(n, N\right) \le \frac{(1: \mathbb{R})}{2} + \frac{1}{(n: \mathbb{R})}))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/AmiriArrazolaHiddenMatchingCloningBound.claim` (`✓ std3`).

*Citation.* Ryan Amiri and Juan Miguel Arrazola (2016). *Quantum money with nearly optimal error tolerance*. DOI: [10.1103/PhysRevA.95.062334](https://doi.org/10.1103/PhysRevA.95.062334). URL: <https://arxiv.org/abs/1610.06345v1>.

*Commentary.*

Equation (21), p. 8, states F̄ ≤ 1/2 + 1/n. The following sentence, p. 9, is: “which we have verified numerically for n ≤ 14 and we conjecture holds for any n. From now on, we simply assume that n ≤ 14.” The dimensions here are all positive even dimensions, expressed by 2 ≤ n and Even n, and the channel is arbitrary.

**Theorem 1.7 (The mean fidelity bound in every positive even dimension).**

$$\forall (n: \mathbb{N}), ((2 \le n) \Rightarrow ((\operatorname{Even}\left(n\right)) \Rightarrow (\forall (N: \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(n\right), (\operatorname{Fin}\left(n\right)\times\operatorname{Fin}\left(n\right))\right)), (\operatorname{meanFidelity}\left(n, N\right) \le \frac{(1: \mathbb{R})}{2} + \frac{1}{(n: \mathbb{R})}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/AmiriArrazolaHiddenMatchingCloningBound.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ryan Amiri and Juan Miguel Arrazola (2016). *Quantum money with nearly optimal error tolerance*. DOI: [10.1103/PhysRevA.95.062334](https://doi.org/10.1103/PhysRevA.95.062334). URL: <https://arxiv.org/abs/1610.06345v1>.

*Commentary.*

Averaging four binary signs leaves precisely the index patterns in which each coordinate has even multiplicity. This evaluates the performance operator as 1/(2n²) times a nonnegative symmetric matrix L on triples.

For a triple (a,b,c), assign weight 2(n−1) when a=b=c, weight 2 when b=c and a differs, and weight n otherwise. Every weight is positive for n ≥ 2. The weighted row sum of L is at most (n+2) times this weight. The scaled complex quadratic row estimate then bounds its quadratic form by (n+2) times the squared Euclidean norm.

The finite Kraus representation decomposes the input-first Choi matrix into outer products. Its trace is n by trace preservation. The tensor Choi pairing identifies the averaged two-marginal objective with the performance-operator trace. Summing the quadratic bound over the Kraus vectors gives (n+2)/(2n) = 1/2 + 1/n. No symmetry or covariance condition on the channel is used.

This theorem removes the n ≤ 14 restriction for equation (21). It does not assert a uniform attaining channel or the paper's further protocol-security results.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/AmiriArrazolaHiddenMatchingCloningBound.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/AmiriArrazolaHiddenMatchingCloningBound.eta`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/AmiriArrazolaHiddenMatchingCloningBound.meanFidelity`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/AmiriArrazolaHiddenMatchingCloningBound.phi`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/AmiriArrazolaHiddenMatchingCloningBound.result`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/AmiriArrazolaHiddenMatchingCloningBound.rho`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/AmiriArrazolaHiddenMatchingCloningBound.tau`
- Dependency: [D5/S3/Quantum/Entanglement/UniversalReplacementCapacityGrowth](../Entanglement/UniversalReplacementCapacityGrowth.md)
- Dependency: [D5/S3/Quantum/FixedPointProjection](../FixedPointProjection.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../Foundation/FiniteKrausRepresentation.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Foundation/FiniteStateChannel.md)
- Dependency: [D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm](../Information/BinaryStabilizerGraphNormalForm.md)
- Dependency: [D5/S3/Quantum/Information/HedgingMajorityThreshold](../Information/HedgingMajorityThreshold.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/EntanglementAssistedCommunicationValue](EntanglementAssistedCommunicationValue.md)
- Dependency: [D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation](../Recovery/LiJiangPolarPairOptimalityRefutation.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAveraging](../TensorNetworks/CZXParentLindbladianAveraging.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeTwistedGroundRealization](../../VertexAlgebra/LatticeTwistedGroundRealization.md)
- Dependency: [D5/S3/Weil/ProjectiveRayleigh/ScaledComplexQuadraticRowBound](../../Weil/ProjectiveRayleigh/ScaledComplexQuadraticRowBound.md)
