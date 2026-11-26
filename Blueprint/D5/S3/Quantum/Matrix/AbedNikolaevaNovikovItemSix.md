# The sharp qubit spectral-mean envelope

## Abstract

The spectral geometric mean has sharp relative trace-violation envelope 1/√(1−δ²)−1 in complex dimension two.

**Definition 1.1 (Relative violation for a fixed density).**

$$\forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), \operatorname{V}\left(rho\right) = \operatorname{sSup}\left(\{r: \mathbb{R} | \exists (A: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), \exists (B: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\operatorname{PosDef}\left(A\right) \land (\operatorname{PosDef}\left(B\right) \land r = \frac{((\operatorname{bornProbability}\left(rho, \operatorname{specMean}\left(A, B, \frac{1}{2}\right)\right)).re - \operatorname{sqrt}\left((\operatorname{bornProbability}\left(rho, A\right)).re \cdot (\operatorname{bornProbability}\left(rho, B\right)).re\right))}{\operatorname{sqrt}\left((\operatorname{bornProbability}\left(rho, A\right)).re \cdot (\operatorname{bornProbability}\left(rho, B\right)).re\right)}))\}\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovItemSix.V` (`✓ std3`).

*Citation.* Sami Abdullah Abed; Irina Nikolaeva; Andrej Novikov (2026). *How characterisations of traces and central elements fail: sharp violation constants via Michelson contrast and noncentrality*. DOI: [10.48550/arXiv.2610.34388](https://doi.org/10.48550/arXiv.2610.34388). URL: <https://arxiv.org/abs/2610.34388v1>.

*Commentary.*

Section 3.4, p. 10: “For a fixed density V(ρ) denotes its supremum, and the envelope Vₙ(δ) is the supremum of V(ρ) over all ρ in Mₙ with OMC(ρ) = δ.” V is the real supremum of (L−R)/R for item 6. The real trace functional is Complex.re of FiniteDimensional.bornProbability. The spectral geometric mean is SpectralGeometricLogEuclideanRefutation.specMean at real weight 1/2. A and B range over all positive definite complex 2×2 matrices; no commutation or trace-one assumption is imposed.

**Definition 1.2 (Envelope at a prescribed contrast).**

$$\forall (delta: \mathbb{R}), \operatorname{envelope}\left(delta\right) = \operatorname{sSup}\left(\{r: \mathbb{R} | \exists (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\operatorname{PosDef}\left(rho\right) \land (\operatorname{contrast}\left(rho\right) = delta \land r = \operatorname{V}\left(rho\right)))\}\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovItemSix.envelope` (`✓ std3`).

*Citation.* Sami Abdullah Abed; Irina Nikolaeva; Andrej Novikov (2026). *How characterisations of traces and central elements fail: sharp violation constants via Michelson contrast and noncentrality*. DOI: [10.48550/arXiv.2610.34388](https://doi.org/10.48550/arXiv.2610.34388). URL: <https://arxiv.org/abs/2610.34388v1>.

*Commentary.*

Section 3.4, p. 10: “For a fixed density V(ρ) denotes its supremum, and the envelope Vₙ(δ) is the supremum of V(ρ) over all ρ in Mₙ with OMC(ρ) = δ.” The contrast is (M−m)/(M+m), with M the supremum and m the infimum of the real spectrum, as in Section 3.2. The supremum ranges over every positive definite complex qubit density with this contrast, with arbitrary positive scale.

**Definition 1.3 (Conjecture 11.1, item 6).**

$$claim = \forall (delta: \mathbb{R}), (0 \le delta \Rightarrow (delta < 1 \Rightarrow \operatorname{envelope}\left(delta\right) = (\frac{1}{\operatorname{sqrt}\left((1 - delta^{2})\right)} - 1)))$$

*Formalization.* `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovItemSix.claim` (`✓ std3`).

*Citation.* Sami Abdullah Abed; Irina Nikolaeva; Andrej Novikov (2026). *How characterisations of traces and central elements fail: sharp violation constants via Michelson contrast and noncentrality*. DOI: [10.48550/arXiv.2610.34388](https://doi.org/10.48550/arXiv.2610.34388). URL: <https://arxiv.org/abs/2610.34388v1>.

*Commentary.*

Abed, Nikolaeva and Novikov, arXiv:2610.34388v1, p. 57, Conjecture 11.1: “Vₙ = G² − 1 for item 7 and Vₙ = g₂₅(δ) for item 25 in every dimension; V₂ = G − 1 for item 6; the value of Proposition 5.17 holds for item 9 in every dimension; and the lower bound of Proposition 5.22 is the two-contrast envelope of item 8 for even n.” The selected clause is V₂=G−1 for item 6. Here G=1/√(1−δ²), δ ranges over [0,1), and envelope is V₂. The other clauses of the conjecture are separate assertions.

**Theorem 1.4 (The sharp spectral-mean envelope).**

$$\forall (delta: \mathbb{R}), (0 \le delta \Rightarrow (delta < 1 \Rightarrow \operatorname{envelope}\left(delta\right) = (\frac{1}{\operatorname{sqrt}\left((1 - delta^{2})\right)} - 1)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovItemSix.result` (`✓ std3`). ∎

*Resolves.* `Problems/ann-item-six` (proved) by `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovItemSix.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ann-item-six","declaration_gid":"D5/S3/Quantum/Matrix/AbedNikolaevaNovikovItemSix.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sami Abdullah Abed; Irina Nikolaeva; Andrej Novikov (2026). *How characterisations of traces and central elements fail: sharp violation constants via Michelson contrast and noncentrality*. DOI: [10.48550/arXiv.2610.34388](https://doi.org/10.48550/arXiv.2610.34388). URL: <https://arxiv.org/abs/2610.34388v1>.

*Commentary.*

Abed, Nikolaeva and Novikov, arXiv:2610.34388v1, p. 57, Conjecture 11.1: “Vₙ = G² − 1 for item 7 and Vₙ = g₂₅(δ) for item 25 in every dimension; V₂ = G − 1 for item 6; the value of Proposition 5.17 holds for item 9 in every dimension; and the lower bound of Proposition 5.22 is the two-contrast envelope of item 8 for even n.” The item-6 equality holds for the entire faithful interval. A completed square controls the two-dimensional off-diagonal contribution. The trace/determinant identity for contrast yields the uniform upper bound after unitary diagonalization. Positive definite matrices approaching a rank-one limit give the lower bound for a density of each contrast. Both suprema are nonempty and bounded above on this interval. A written corollary transfers the value to each faithful qubit density of the prescribed contrast by unitary conjugation and positive rescaling.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovItemSix.V`
- Truth anchor: `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovItemSix.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovItemSix.envelope`
- Truth anchor: `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovItemSix.result`
- Dependency: [D5/S3/Quantum/Bogoliubov/HardyBlockConservation](../Bogoliubov/HardyBlockConservation.md)
- Dependency: [D5/S3/Quantum/FiniteDimensional](../FiniteDimensional.md)
- Dependency: [D5/S3/Quantum/Matrix/AbedNikolaevaNovikovAFDensityBound](AbedNikolaevaNovikovAFDensityBound.md)
- Dependency: [D5/S3/Quantum/Matrix/AbedNikolaevaNovikovTwoContrastYoung](AbedNikolaevaNovikovTwoContrastYoung.md)
- Dependency: [D5/S3/Quantum/Matrix/AlternativeMeanLinearization](AlternativeMeanLinearization.md)
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](CartesianVariance.md)
- Dependency: [D5/S3/Quantum/Matrix/SpectralGeometricLogEuclideanRefutation](SpectralGeometricLogEuclideanRefutation.md)
- Dependency: [D5/S3/Quantum/Matrix/SpectralPower](SpectralPower.md)
- Dependency: [D5/S3/TotalVariation/Hellinger](../../TotalVariation/Hellinger.md)
