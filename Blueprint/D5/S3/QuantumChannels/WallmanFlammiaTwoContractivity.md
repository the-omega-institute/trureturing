# Wallman–Flammia two-contractivity

## Abstract

Every nonunitary channel is two-contractive under a finite exact unitary two-design.

**Definition 1.1 (Exact second unitary moment).**

$$\forall d \in \mathbb{N},\; \forall G \in \operatorname{Subgroup}\left(\operatorname{Matrix}.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right),\; [\operatorname{Fintype}\left(G\right)], \operatorname{IsUnitaryTwoDesign}\left(G\right) = \left(\operatorname{HSMul}.\operatorname{hSMul}\left(((\operatorname{Fintype}.\operatorname{card}\left(G\right): \mathbb{C}))^{-1}, \sum_{g: G} (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{RandomCircuits}.\operatorname{HaarTwoCopyTwirl}.\operatorname{literalMoment}\left(\operatorname{val}\left(\operatorname{val}\left(g\right)\right)\right))\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{RandomCircuits}.\operatorname{HaarTwoCopyTwirl}.\operatorname{haarAverage}\left(\operatorname{Fin}\left(d\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/WallmanFlammiaTwoContractivity.IsUnitaryTwoDesign` (`✓ std3`).

*Citation.* Joel J. Wallman; Steven T. Flammia (2014). *Randomized Benchmarking with Confidence*. DOI: [10.1088/1367-2630/16/10/103032](https://doi.org/10.1088/1367-2630/16/10/103032). URL: <https://arxiv.org/abs/1404.6025v4>.

*Commentary.*

Section II, PDF page 2: “we require G to be a unitary 2-design (e.g., the Clifford group on n qubits for d=2ⁿ), meaning that sampling over G reproduces the second moments of the Haar measure”. The finite subgroup carries its uniform distribution. HaarTwoCopyTwirl.literalMoment orders the four factors as two conjugate matrices followed by two original matrices.

**Definition 1.2 (A matrix entry of the conjugated channel).**

$$\forall d \in \mathbb{N},\; \forall Lambda \in \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right),\; \forall U \in \operatorname{Matrix}.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall r \in \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right),\; \forall c \in \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right),\; \operatorname{conjugatedEntry}\left(Lambda, U, r, c\right) = \left(\operatorname{val}\left(U\right) \cdot (\operatorname{CStarMatrix}.\operatorname{ofMatrix}).symm\left((Lambda).toCompletelyPositiveMap\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}\left(\operatorname{Matrix}.\operatorname{conjTranspose}\left(\operatorname{val}\left(U\right)\right) \cdot \operatorname{Matrix}.\operatorname{single}\left((c).1, (c).2, 1\right) \cdot \operatorname{val}\left(U\right)\right)\right)\right) \cdot \operatorname{Matrix}.\operatorname{conjTranspose}\left(\operatorname{val}\left(U\right)\right)\right)\left((r).1, (r).2\right)$$

*Formalization.* `D5/S3/QuantumChannels/WallmanFlammiaTwoContractivity.conjugatedEntry` (`✓ std3`).

*Citation.* Joel J. Wallman; Steven T. Flammia (2014). *Randomized Benchmarking with Confidence*. DOI: [10.1088/1367-2630/16/10/103032](https://doi.org/10.1088/1367-2630/16/10/103032). URL: <https://arxiv.org/abs/1404.6025v4>.

*Commentary.*

Section IV.A, PDF page 8: “Given a rep (φ,V) of a group G, a matrix A∈GL(V) and an element g∈G, we define Aᵍ = φ(g)Aφ(g⁻¹).” Matrix.single supplies the input matrix unit; the row and column indices each range over Fin d × Fin d. The channel acts on the entire complex matrix space.

**Definition 1.3 (Uniform tensor-power twirl).**

$$\forall d \in \mathbb{N},\; \forall Lambda \in \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right),\; \forall G \in \operatorname{Subgroup}\left(\operatorname{Matrix}.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right),\; [\operatorname{Fintype}\left(G\right)], \forall n \in \mathbb{N},\; \operatorname{twirledTensorPower}\left(Lambda, G, n\right) = fun (r: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)) \mapsto fun (c: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)) \mapsto ((\operatorname{Fintype}.\operatorname{card}\left(G\right): \mathbb{C}))^{-1} \cdot \sum_{g: G} (\prod_{k: \operatorname{Fin}\left(n\right)} (\operatorname{conjugatedEntry}\left(Lambda, \operatorname{val}\left(g\right), r\left(k\right), c\left(k\right)\right)))$$

*Formalization.* `D5/S3/QuantumChannels/WallmanFlammiaTwoContractivity.twirledTensorPower` (`✓ std3`).

*Citation.* Joel J. Wallman; Steven T. Flammia (2014). *Randomized Benchmarking with Confidence*. DOI: [10.1088/1367-2630/16/10/103032](https://doi.org/10.1088/1367-2630/16/10/103032). URL: <https://arxiv.org/abs/1404.6025v4>.

*Commentary.*

Section IV.A, PDF page 8: “The uniform average of this action on A is called the G-twirl of A, and is given by Aᴳ = |G|⁻¹∑g∈G Aᵍ.” The n tensor factors are indexed by Fin n. Their matrix-unit entries are multiplied before the uniform average is taken.

**Definition 1.4 (Definition 15).**

$$\forall d \in \mathbb{N},\; \forall Lambda \in \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right),\; \forall G \in \operatorname{Subgroup}\left(\operatorname{Matrix}.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right),\; [\operatorname{Fintype}\left(G\right)], \forall n \in \mathbb{N},\; \operatorname{IsNContractive}\left(Lambda, G, n\right) = \left(\operatorname{Multiset}.\operatorname{card}\left(\operatorname{Multiset}.\operatorname{filter}\left(fun (z: \mathbb{C}) \mapsto \left\lVert z \right\rVert = 1, \operatorname{Polynomial}.\operatorname{roots}\left(\operatorname{Matrix}.\operatorname{charpoly}\left(\operatorname{twirledTensorPower}\left(Lambda, G, n\right)\right)\right)\right)\right) \le 1\right)$$

*Formalization.* `D5/S3/QuantumChannels/WallmanFlammiaTwoContractivity.IsNContractive` (`✓ std3`).

*Citation.* Joel J. Wallman; Steven T. Flammia (2014). *Randomized Benchmarking with Confidence*. DOI: [10.1088/1367-2630/16/10/103032](https://doi.org/10.1088/1367-2630/16/10/103032). URL: <https://arxiv.org/abs/1404.6025v4>.

*Commentary.*

Definition 15, PDF page 23: “A channel Λ:Dd → Dd is n-contractive with respect to a group G⊆U(d) if (Λ⊗n)ᴳ has at most one eigenvalue of modulus 1.” The roots of the characteristic polynomial form a multiset, so the count includes algebraic multiplicity.

**Definition 1.5 (The conjecture before Proposition 16).**

$$claim = (\forall d \in \mathbb{N},\; (2 \le d) \Rightarrow (\forall Lambda \in \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right),\; \forall G \in \operatorname{Subgroup}\left(\operatorname{Matrix}.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right),\; [\operatorname{Fintype}\left(G\right)], (\operatorname{IsUnitaryTwoDesign}\left(G\right)) \Rightarrow ((\neg (\exists U \in \operatorname{Matrix}.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{CStarMatrix}.\operatorname{ofMatrix}).symm\left((Lambda).toCompletelyPositiveMap\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}\left(X\right)\right)\right) = \operatorname{val}\left(U\right) \cdot X \cdot \operatorname{Matrix}.\operatorname{conjTranspose}\left(\operatorname{val}\left(U\right)\right))) \Rightarrow (\operatorname{IsNContractive}\left(Lambda, G, 2\right)))))$$

*Formalization.* `D5/S3/QuantumChannels/WallmanFlammiaTwoContractivity.claim` (`✓ std3`).

*Citation.* Joel J. Wallman; Steven T. Flammia (2014). *Randomized Benchmarking with Confidence*. DOI: [10.1088/1367-2630/16/10/103032](https://doi.org/10.1088/1367-2630/16/10/103032). URL: <https://arxiv.org/abs/1404.6025v4>.

*Commentary.*

Section VII, PDF page 24: “We conjecture that all nonunitary channels are in fact 2-contractive with respect to any unitary 2-design.” The dimension is any natural number at least two. QuantumChannel supplies complete positivity and trace preservation. The subgroup is finite, its second moment is exact, and no unitary conjugation agrees with the channel on every input matrix.

**Theorem 1.6 (Unrestricted two-contractivity).**

$$\forall d \in \mathbb{N},\; (2 \le d) \Rightarrow (\forall Lambda \in \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right),\; \forall G \in \operatorname{Subgroup}\left(\operatorname{Matrix}.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right),\; [\operatorname{Fintype}\left(G\right)], (\operatorname{IsUnitaryTwoDesign}\left(G\right)) \Rightarrow ((\neg (\exists U \in \operatorname{Matrix}.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{CStarMatrix}.\operatorname{ofMatrix}).symm\left((Lambda).toCompletelyPositiveMap\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}\left(X\right)\right)\right) = \operatorname{val}\left(U\right) \cdot X \cdot \operatorname{Matrix}.\operatorname{conjTranspose}\left(\operatorname{val}\left(U\right)\right))) \Rightarrow (\operatorname{IsNContractive}\left(Lambda, G, 2\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/WallmanFlammiaTwoContractivity.result` (`✓ std3`). ∎

*Resolves.* `Problems/wf1404` (proved) by `D5/S3/QuantumChannels/WallmanFlammiaTwoContractivity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wf1404","declaration_gid":"D5/S3/QuantumChannels/WallmanFlammiaTwoContractivity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Joel J. Wallman; Steven T. Flammia (2014). *Randomized Benchmarking with Confidence*. DOI: [10.1088/1367-2630/16/10/103032](https://doi.org/10.1088/1367-2630/16/10/103032). URL: <https://arxiv.org/abs/1404.6025v4>.

*Commentary.*

The second moment makes both averaged Gram matrices scalar multiples of the traceless projection. A rectangular factorization bounds the full traceless tensor square, including complex non-Hermitian directions. Choi purity makes the scalar strictly less than one for every nonunitary channel. In trace-adapted coordinates the four diagonal tensor sectors are the scalar identity, two strictly contractive one-copy blocks, and the strictly contractive traceless tensor square. Their characteristic polynomials leave exactly one root on the unit circle. The nonunital entries occupy lower blocks and do not change this factorization.

## References

- Truth anchor: `D5/S3/QuantumChannels/WallmanFlammiaTwoContractivity.IsNContractive`
- Truth anchor: `D5/S3/QuantumChannels/WallmanFlammiaTwoContractivity.IsUnitaryTwoDesign`
- Truth anchor: `D5/S3/QuantumChannels/WallmanFlammiaTwoContractivity.claim`
- Truth anchor: `D5/S3/QuantumChannels/WallmanFlammiaTwoContractivity.conjugatedEntry`
- Truth anchor: `D5/S3/QuantumChannels/WallmanFlammiaTwoContractivity.result`
- Truth anchor: `D5/S3/QuantumChannels/WallmanFlammiaTwoContractivity.twirledTensorPower`
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumBall](../Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumBall.md)
- Dependency: [D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability](../Quantum/Entanglement/ConicalDesignConcurrenceComparability.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Quantum/Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../Quantum/Foundation/FiniteKrausRepresentation.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Quantum/Foundation/FiniteStateChannel.md)
- Dependency: [D5/S3/Quantum/GNSMatrix](../Quantum/GNSMatrix.md)
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../Quantum/Matrix/CartesianVariance.md)
- Dependency: [D5/S3/Quantum/RandomCircuits/CHaarConcatenationNonmonotone](../Quantum/RandomCircuits/CHaarConcatenationNonmonotone.md)
- Dependency: [D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl](../Quantum/RandomCircuits/HaarTwoCopyTwirl.md)
- Dependency: [D5/S3/Quantum/Recovery/ActualChannelAlgebra](../Quantum/Recovery/ActualChannelAlgebra.md)
- Dependency: [D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation](../Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.md)
- Dependency: [D5/S3/QuantumBounds/PeritoTsirelson](../QuantumBounds/PeritoTsirelson.md)
