# Formation is not constant on the three-vector subspace

## Abstract

A nonorthogonal ensemble lowers formation on the Song–Chen–Djokovic subspace.

Coordinates use zero-based Fin indices and complex amplitudes. Real square roots are embedded into the complex numbers. The operation rankOneDensity is Matrix.vecMulVec v (star v); partialTraceRight traces out the second factor. FormationBounds.E_F takes the infimum of finite-ensemble marginal entropy costs, in bits.

**Definition 1.1 (G).**

$$\forall i \in \operatorname{Fin}\left(9\right),\; \forall j \in \operatorname{Fin}\left(9\right),\; \operatorname{G}\left(i, j\right) = \operatorname{ite}\left((i = 0) \land (j = 0), \frac{2}{3}, \operatorname{ite}\left((i = 1) \land (j = 1), \frac{1}{(\operatorname{Real}.\operatorname{sqrt}\left(3\right):\mathbb{C})}, \operatorname{ite}\left((i = 1) \land (j = 5), \frac{\operatorname{Complex}.\operatorname{I}}{3 \cdot (\operatorname{Real}.\operatorname{sqrt}\left(3\right):\mathbb{C})}, \operatorname{ite}\left((i = 1) \land (j = 6), \frac{2}{3 \cdot (\operatorname{Real}.\operatorname{sqrt}\left(3\right):\mathbb{C})}, \operatorname{ite}\left((i = 2) \land (j = 2), \frac{(\operatorname{Real}.\operatorname{sqrt}\left(2\right):\mathbb{C})}{3}, \operatorname{ite}\left((i = 3) \land (j = 3), \frac{1}{(\operatorname{Real}.\operatorname{sqrt}\left(3\right):\mathbb{C})}, \operatorname{ite}\left((i = 4) \land (j = 4), \frac{(\operatorname{Real}.\operatorname{sqrt}\left(2\right):\mathbb{C})}{3}, \operatorname{ite}\left((i = 5) \land (j = 5), \frac{(\operatorname{Real}.\operatorname{sqrt}\left(11\right):\mathbb{C})}{3 \cdot (\operatorname{Real}.\operatorname{sqrt}\left(3\right):\mathbb{C})}, \operatorname{ite}\left((i = 5) \land (j = 6), \frac{(3 + 2 \cdot \operatorname{Complex}.\operatorname{I})}{3 \cdot (\operatorname{Real}.\operatorname{sqrt}\left(33\right):\mathbb{C})}, \operatorname{ite}\left((i = 6) \land (j = 6), \frac{1}{(\operatorname{Real}.\operatorname{sqrt}\left(33\right):\mathbb{C})}, \operatorname{ite}\left((i = 7) \land (j = 7), \frac{2}{3}, \operatorname{ite}\left((i = 8) \land (j = 8), \frac{1}{(\operatorname{Real}.\operatorname{sqrt}\left(3\right):\mathbb{C})}, 0\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphDensity/UniqueBasisFormationRefutation.G` (`✓ std3`).

*Citation.* Zhiwei Song, Lin Chen and Dragomir Z. Djokovic (2024). *The existence of distinguishable bases in three-dimensional subspaces of qutrit-qudit systems under one-way local operations and classical communication*. DOI: [10.1109/TIT.2024.3435412](https://doi.org/10.1109/TIT.2024.3435412). URL: <https://arxiv.org/abs/2307.01980v3>.

*Commentary.*

Song–Chen–Djokovic, Eq. (2), arXiv v3 p. 2: the displayed conditional expression lists all twelve nonzero entries of G, with row and column indices decreased by one.

**Definition 1.2 (Psi).**

$$\forall k \in \operatorname{Fin}\left(3\right),\; \forall ab \in (\operatorname{Fin}\left(3\right))\times(\operatorname{Fin}\left(9\right)),\; \operatorname{Psi}\left(k\right)\left(ab\right) = \operatorname{G}\left(ab.2, \operatorname{Fin}.\operatorname{mk}\left(3 \cdot \operatorname{val}\left(ab.1\right) + \operatorname{val}\left(k\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphDensity/UniqueBasisFormationRefutation.Psi` (`✓ std3`).

*Citation.* Zhiwei Song, Lin Chen and Dragomir Z. Djokovic (2024). *The existence of distinguishable bases in three-dimensional subspaces of qutrit-qudit systems under one-way local operations and classical communication*. DOI: [10.1109/TIT.2024.3435412](https://doi.org/10.1109/TIT.2024.3435412). URL: <https://arxiv.org/abs/2307.01980v3>.

*Commentary.*

Eq. (3), arXiv v3 p. 2: |Ψ₁⟩ = |1⟩⊗|r₁⟩ + |2⟩⊗|r₄⟩ + |3⟩⊗|r₇⟩, |Ψ₂⟩ = |1⟩⊗|r₂⟩ + |2⟩⊗|r₅⟩ + |3⟩⊗|r₈⟩, |Ψ₃⟩ = |1⟩⊗|r₃⟩ + |2⟩⊗|r₆⟩ + |3⟩⊗|r₉⟩, where |r_i⟩ is the i-th column vector of G. Thus Psi k (a,b) is the b-entry of column 3a+k; Fin.mk forms its column index and its omitted proof verifies that it is below 9.

**Definition 1.3 (spanPsi).**

$$spanPsi = \operatorname{Submodule}.\operatorname{span}\left(\mathbb{C}, \operatorname{Set}.\operatorname{range}\left(Psi\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphDensity/UniqueBasisFormationRefutation.spanPsi` (`✓ std3`).

*Citation.* Zhiwei Song, Lin Chen and Dragomir Z. Djokovic (2024). *The existence of distinguishable bases in three-dimensional subspaces of qutrit-qudit systems under one-way local operations and classical communication*. DOI: [10.1109/TIT.2024.3435412](https://doi.org/10.1109/TIT.2024.3435412). URL: <https://arxiv.org/abs/2307.01980v3>.

*Commentary.*

The subspace S is the complex span of Ψ₁, Ψ₂ and Ψ₃. Set.range Psi includes exactly the three zero-based choices of k.

**Definition 1.4 (claim).**

$$claim = \left(\forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(3\right))\times(\operatorname{Fin}\left(9\right)), (\operatorname{Fin}\left(3\right))\times(\operatorname{Fin}\left(9\right)), \mathbb{C}\right),\; (\operatorname{Matrix}.\operatorname{PosSemidef}\left(rho\right)) \Rightarrow ((\operatorname{Matrix}.\operatorname{trace}\left(rho\right) = 1) \Rightarrow ((\operatorname{LinearMap}.\operatorname{range}\left(\operatorname{Matrix}.\operatorname{toLin}'\left(rho\right)\right) \le spanPsi) \Rightarrow (\operatorname{FormationBounds}.E_F\left(rho\right) = \operatorname{FormationBounds}.E_F\left(\operatorname{rankOneDensity}\left(\operatorname{Psi}\left(0\right)\right)\right))))\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphDensity/UniqueBasisFormationRefutation.claim` (`✓ std3`).

*Citation.* Zhiwei Song, Lin Chen and Dragomir Z. Djokovic (2024). *The existence of distinguishable bases in three-dimensional subspaces of qutrit-qudit systems under one-way local operations and classical communication*. DOI: [10.1109/TIT.2024.3435412](https://doi.org/10.1109/TIT.2024.3435412). URL: <https://arxiv.org/abs/2307.01980v3>.

*Commentary.*

Song–Chen–Djokovic, arXiv v3 p. 3: Further, by calculation one can see that every state in the span of the three states has entanglement more than 1.52 ebits. Hence, the entanglement of formation (EOF) of every mixed state whose range is contained in the span is also more than 1.52 ebits [19]. We don't know whether this EOF is exactly equal to that of the pure state |Ψ₁⟩. The matrix rho ranges over all density operators on Fin 3 × Fin 9; positivity, trace one and range inclusion express the source's mixed-state domain. Its comparison state is rankOneDensity(Psi 0).

**Theorem 1.5 (Positive-weight components of a pure state differ only by phase).**

$$\forall p \in \mathbb{N},\; \forall q \in \mathbb{N},\; \forall v \in ((\operatorname{Fin}\left(p\right))\times (\operatorname{Fin}\left(q\right)))\to \mathbb{C},\; (\sum_{x:(\operatorname{Fin}\left(p\right))\times (\operatorname{Fin}\left(q\right))} \Vert v\left(x\right) \Vert^2 = 1) \Rightarrow (\forall e \in \operatorname{Ensemble}\left(\operatorname{rankOneDensity}\left(v\right)\right),\; \forall i \in \operatorname{Fin}\left(e.\operatorname{N}\right),\; (0 < e.\operatorname{weight}\left(i\right)) \Rightarrow (\exists z \in \mathbb{C},\; (\Vert z \Vert = 1) \land (e.\operatorname{psi}\left(i\right) = z\cdot v)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GraphDensity/UniqueBasisFormationRefutation.positive_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zhiwei Song, Lin Chen and Dragomir Z. Djokovic (2024). *The existence of distinguishable bases in three-dimensional subspaces of qutrit-qudit systems under one-way local operations and classical communication*. DOI: [10.1109/TIT.2024.3435412](https://doi.org/10.1109/TIT.2024.3435412). URL: <https://arxiv.org/abs/2307.01980v3>.

*Commentary.*

For arbitrary natural dimensions p and q, let v be a unit vector and e a finite ensemble whose average is rankOneDensity v. Every component e.psi i with strictly positive weight is z times v for a complex scalar z of norm one. The ensemble's kernel constraints force all two-coordinate minors of v and e.psi i to vanish, so the vectors are proportional; their unit norms fix the modulus of the scalar.

**Theorem 1.6 (The equality fails).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GraphDensity/UniqueBasisFormationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/song-chen-djokovic-2023-unique-basis-eof` (refuted) by `D5/S3/Quantum/Entanglement/GraphDensity/UniqueBasisFormationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"song-chen-djokovic-2023-unique-basis-eof","declaration_gid":"D5/S3/Quantum/Entanglement/GraphDensity/UniqueBasisFormationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Zhiwei Song, Lin Chen and Dragomir Z. Djokovic (2024). *The existence of distinguishable bases in three-dimensional subspaces of qutrit-qudit systems under one-way local operations and classical communication*. DOI: [10.1109/TIT.2024.3435412](https://doi.org/10.1109/TIT.2024.3435412). URL: <https://arxiv.org/abs/2307.01980v3>.

*Commentary.*

Set Pj=rankOneDensity(Psi j). The density (P0+P1+P2)/3 has range in spanPsi. The four ensemble vectors are (Psi 0 + sqrt(3) • Psi 1)/2, (Psi 0 - sqrt(3) • Psi 1)/2, Psi 0 and Psi 2, with weights 2/9, 2/9, 2/9 and 1/3. The first two marginals have spectrum (17,10,9)/36. Their entropy Hstar is strictly below H0=H(4/9,1/3,2/9), by 2^102 < 17^17·5^10·3^6 and the logarithm laws. The ensemble cost is (4/9)Hstar+(5/9)H0, hence strictly below H0. Every positive-weight component of an ensemble of a unit pure state is a unit phase multiple; zero-weight components vanish from the cost. Thus E_F(P0)=H0, and the finite-ensemble upper bound contradicts claim.

This supplies a strict upper bound for the density's formation, not its exact infimum. The general positive diagonal-weight family is a neighbouring question. The numerical values H0=1.5304930568, Hstar=1.5244951608 and cost=1.5278273252 are compatible with the source's 1.52-ebit lower bound. These values are computed by the independent experiment check.py in the-omega-institute/trureturing-experiments, commit e0c03b28bb524e37942a1e8ae9687e92ffa7c0ac; they are not decimal kernel conclusions.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/UniqueBasisFormationRefutation.G`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/UniqueBasisFormationRefutation.Psi`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/UniqueBasisFormationRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/UniqueBasisFormationRefutation.positive_phase`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/UniqueBasisFormationRefutation.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/UniqueBasisFormationRefutation.spanPsi`
- Dependency: [D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation](../../../Combinatorics/Graph/DomiRankEntropyRefutation.md)
- Dependency: [D5/S3/Entropy/EntropyNonneg](../../../Entropy/EntropyNonneg.md)
- Dependency: [D5/S3/Observer/Existence/EmpiricalReflexiveSeparation](../../../Observer/Existence/EmpiricalReflexiveSeparation.md)
- Dependency: [D5/S3/Quantum/Algebra/CStarSmaleHigherOrder](../../Algebra/CStarSmaleHigherOrder.md)
- Dependency: [D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds](FormationBounds.md)
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../../Matrix/CartesianVariance.md)
