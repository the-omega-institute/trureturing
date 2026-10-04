# Normalized Bloch weights and finite orbit support

## Abstract

Normalized Bloch weights and finite orbit support

**Definition 1.1 (State).**

$$\forall m \in \mathbb{N},\; \operatorname{State}\left(m\right) = \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Stationing}\left(2 \cdot m\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/SpectralComparison.State` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The computational spin basis carries the Hilbert L2 norm; it is not the pointwise supremum norm.

**Definition 1.2 (psiVector).**

$$\forall m \in \mathbb{N},\; \operatorname{psiVector}\left(m\right) = \operatorname{toLp}\left(2, x:\operatorname{Stationing}\left(2 \cdot m\right) \mapsto \operatorname{castComplex}\left(\operatorname{psi}\left(m, x\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/SpectralComparison.psiVector` (`✓ std3`).

*Citation.* Zimeng Li; Ning Wu (2026). *Exact momentum-space analysis of small spin-1/2 J1-J2 rings*. DOI: [10.48550/arXiv.2604.23149](https://doi.org/10.48550/arXiv.2604.23149). URL: <https://arxiv.org/abs/2604.23149v1>.

*Commentary.*

The integer coefficients of Eq. (6) are embedded in the complex Hilbert state.

**Definition 1.3 (phase).**

$$\forall m \in \mathbb{N},\; \forall t \in \operatorname{Fin}\left(2 \cdot m\right),\; \forall j \in \operatorname{Fin}\left(2 \cdot m\right),\; \operatorname{phase}\left(m, t, j\right) = \operatorname{ComplexExp}\left(\frac{\operatorname{castComplex}\left(2\right) \cdot \operatorname{castComplex}\left(\pi\right) \cdot \operatorname{I} \cdot \operatorname{castComplex}\left(\operatorname{val}\left(t\right)\right) \cdot \operatorname{castComplex}\left(\operatorname{val}\left(j\right)\right)}{\operatorname{castComplex}\left(2 \cdot m\right)}\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/SpectralComparison.phase` (`✓ std3`).

*Citation.* Zimeng Li; Ning Wu (2026). *Exact momentum-space analysis of small spin-1/2 J1-J2 rings*. DOI: [10.48550/arXiv.2604.23149](https://doi.org/10.48550/arXiv.2604.23149). URL: <https://arxiv.org/abs/2604.23149v1>.

*Commentary.*

The phase is exp(2 pi i t j/(2m)). CastComplex embeds every natural or real factor in the complex field; division here is complex division. Momentum t=m is pi, equivalent to -pi.

**Definition 1.4 (bloch).**

$$\forall m \in \mathbb{N},\; \forall x \in \operatorname{Stationing}\left(2 \cdot m\right),\; \forall t \in \operatorname{Fin}\left(2 \cdot m\right),\; \operatorname{bloch}\left(m, x, t\right) = \sum_{j:\operatorname{Fin}\left(2 \cdot m\right)} \operatorname{smul}\left(\operatorname{phase}\left(m, t, j\right), \operatorname{single}\left(\operatorname{iterate}\left(\operatorname{shift}\left(m\right), \operatorname{val}\left(j\right), x\right), \operatorname{castComplex}\left(1\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/SpectralComparison.bloch` (`✓ std3`).

*Citation.* Zimeng Li; Ning Wu (2026). *Exact momentum-space analysis of small spin-1/2 J1-J2 rings*. DOI: [10.48550/arXiv.2604.23149](https://doi.org/10.48550/arXiv.2604.23149). URL: <https://arxiv.org/abs/2604.23149v1>.

*Commentary.*

Li and Wu, p. 4, Eq. (7): "|ξ1(k)⟩ = e^{ik/2}/√6 Σ_{j=0}^{5} e^{ikj} T^j |1, 2⟩, |ξ2(k)⟩ = e^{ik}/√6 Σ_{j=0}^{5} e^{ikj} T^j |1, 3⟩, |ξ3(k)⟩ = e^{i3k/2}/√3 Σ_{j=0}^{2} e^{ikj} T^j |1, 4⟩, (7)". The general vector sums all 2m translations before normalization; repeated orbit points add as amplitudes. The full-period and orbit-period sums give the same normalized ray when nonzero. The paper excludes momenta where the Bloch sum vanishes.

**Definition 1.5 (weight).**

$$\forall m \in \mathbb{N},\; \forall x \in \operatorname{Stationing}\left(2 \cdot m\right),\; \forall t \in \operatorname{Fin}\left(2 \cdot m\right),\; \operatorname{weight}\left(m, x, t\right) = \frac{(\Vert \operatorname{inner}\left(\mathbb{C}, \operatorname{bloch}\left(m, x, t\right), \operatorname{psiVector}\left(m\right)\right)\Vert)^{2}}{(\Vert \operatorname{bloch}\left(m, x, t\right)\Vert)^{2} \cdot (\Vert \operatorname{psiVector}\left(m\right)\Vert)^{2}}$$

*Formalization.* `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/SpectralComparison.weight` (`✓ std3`).

*Citation.* Zimeng Li; Ning Wu (2026). *Exact momentum-space analysis of small spin-1/2 J1-J2 rings*. DOI: [10.48550/arXiv.2604.23149](https://doi.org/10.48550/arXiv.2604.23149). URL: <https://arxiv.org/abs/2604.23149v1>.

*Commentary.*

The squared overlap is divided by the squared Hilbert norms of both vectors. This is the weight in the normalized Bloch basis; the inner product conjugates its first argument.

**Theorem 1.6 (spectral_comparison).**

$$\forall m \in \mathbb{N},\; [\operatorname{NeZero}\left(2 \cdot m\right)] (1 \le m) \Rightarrow ((\forall t \in \operatorname{Fin}\left(2 \cdot m\right),\; (\Vert \operatorname{bloch}\left(m, \operatorname{block}\left(m\right), t\right)\Vert)^{2} = \operatorname{castReal}\left(2 \cdot m\right)) \land ((\forall t \in \operatorname{Fin}\left(2 \cdot m\right),\; (\operatorname{val}\left(t\right) = m) \Rightarrow (\operatorname{weight}\left(m, \operatorname{block}\left(m\right), t\right) = \frac{\operatorname{castReal}\left(2 \cdot m\right) \cdot (\operatorname{castReal}\left(\operatorname{K}\left(m\right)\right))^{2}}{(\Vert \operatorname{psiVector}\left(m\right)\Vert)^{2}})) \land ((\forall x \in \operatorname{Stationing}\left(2 \cdot m\right),\; \forall t \in \operatorname{Fin}\left(2 \cdot m\right),\; (\operatorname{bloch}\left(m, x, t\right) \ne 0) \Rightarrow ((\neg (\operatorname{isArc}\left(m, x\right))) \Rightarrow (\operatorname{weight}\left(m, x, t\right) < \frac{\operatorname{castReal}\left(2 \cdot m\right) \cdot (\operatorname{castReal}\left(\operatorname{K}\left(m\right)\right))^{2}}{(\Vert \operatorname{psiVector}\left(m\right)\Vert)^{2}}))) \land (\forall x \in \operatorname{Stationing}\left(2 \cdot m\right),\; \forall t \in \operatorname{Fin}\left(2 \cdot m\right),\; (\operatorname{val}\left(t\right) \ne m) \Rightarrow (\operatorname{weight}\left(m, x, t\right) = 0)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/SpectralComparison.spectral_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The block translations are distinct and its Bloch norm squared is 2m. The translation eigenvalue gives zero overlap at every other momentum. A non-arc Bloch vector is supported on at most 2m configurations with strict coefficient deficits; Cauchy-Schwarz on that support gives the strict normalized weight deficit.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/SpectralComparison.State`
- Truth anchor: `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/SpectralComparison.bloch`
- Truth anchor: `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/SpectralComparison.phase`
- Truth anchor: `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/SpectralComparison.psiVector`
- Truth anchor: `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/SpectralComparison.spectral_comparison`
- Truth anchor: `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/SpectralComparison.weight`
- Dependency: [D5/S1/Phase/SeatTowerCombinatorics](../../../../S1/Phase/SeatTowerCombinatorics.md)
- Dependency: [D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/ArcCoefficients](ArcCoefficients.md)
- Dependency: [D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients](PairingCoefficients.md)
