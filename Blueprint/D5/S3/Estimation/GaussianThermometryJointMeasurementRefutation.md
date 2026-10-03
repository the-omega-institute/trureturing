# Refutation of the local-versus-global Gaussian thermometry conjecture

## Abstract

The local-versus-global Gaussian thermometry conjecture in Eq. (47) of Cenni, Lami, Acín and Mehboudi is refuted by two unequal-frequency modes.

**Definition 1.1 (Temperature derivative).**

$$\forall omega \in \mathbb{R},\; \forall T \in \mathbb{R},\; \operatorname{thermalNuDeriv}\left(omega, T\right) = omega/(2 \cdot T^{2}) \cdot (\operatorname{coth}\left((omega/(2 \cdot T))\right)^{2} + -1)$$

*Formalization.* `D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation.thermalNuDeriv` (`✓ std3`).

*Citation.* M. F. B. Cenni; L. Lami; A. Acín; M. Mehboudi (2022). *Thermometry of Gaussian quantum systems using Gaussian measurements*. URL: <https://arxiv.org/abs/2110.02098v4>.

*Commentary.*

The derivative used in the covariance Fisher information is ν' = (ω/2T²)(ν² − 1), where ν = coth(ω/(2T)). The coth operator is D5.S3.Observer.Fluctuation.ThermalCoefficientFloor.coth, defined as Real.cosh / Real.sinh.

**Definition 1.2 (Product thermal covariance).**

$$\forall m \in \mathbb{N},\; \forall omega \in \operatorname{Fin}\left(m\right) \to \mathbb{R},\; \forall T \in \mathbb{R},\; \forall i \in \operatorname{Fin}\left(2 \cdot m\right),\; \forall j \in \operatorname{Fin}\left(2 \cdot m\right),\; \operatorname{thermalCov}\left(omega, T\right)\left(i, j\right) = \operatorname{if}\left(i = j, \operatorname{coth}\left((omega\left((\operatorname{Fin.mk}\left(\operatorname{Nat.div}\left(\operatorname{Fin.val}\left(i\right), 2\right)\right):\operatorname{Fin}\left(m\right))\right)/(2 \cdot T))\right), 0\right)$$

*Formalization.* `D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation.thermalCov` (`✓ std3`).

*Citation.* M. F. B. Cenni; L. Lami; A. Acín; M. Mehboudi (2022). *Thermometry of Gaussian quantum systems using Gaussian measurements*. URL: <https://arxiv.org/abs/2110.02098v4>.

*Commentary.*

For m product modes, σ is the direct sum of νₖ I₂ blocks. The Fin m constructor uses Nat.div(Fin.val(i),2), integer division, with the bound supplied by Fin.cast(...).divNat. Thus adjacent coordinates share a mode.

**Definition 1.3 (Derivative of the product covariance).**

$$\forall m \in \mathbb{N},\; \forall omega \in \operatorname{Fin}\left(m\right) \to \mathbb{R},\; \forall T \in \mathbb{R},\; \forall i \in \operatorname{Fin}\left(2 \cdot m\right),\; \forall j \in \operatorname{Fin}\left(2 \cdot m\right),\; \operatorname{thermalCovDeriv}\left(omega, T\right)\left(i, j\right) = \operatorname{if}\left(i = j, \operatorname{thermalNuDeriv}\left(omega\left((\operatorname{Fin.mk}\left(\operatorname{Nat.div}\left(\operatorname{Fin.val}\left(i\right), 2\right)\right):\operatorname{Fin}\left(m\right))\right), T\right), 0\right)$$

*Formalization.* `D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation.thermalCovDeriv` (`✓ std3`).

*Citation.* M. F. B. Cenni; L. Lami; A. Acín; M. Mehboudi (2022). *Thermometry of Gaussian quantum systems using Gaussian measurements*. URL: <https://arxiv.org/abs/2110.02098v4>.

*Commentary.*

The derivative is the direct sum of νₖ' I₂ blocks, with the same Fin m quotient index.

**Definition 1.4 (Physical Gaussian measurement covariance).**

$$\forall m \in \mathbb{N},\; \forall sigmaM \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2 \cdot m\right), \operatorname{Fin}\left(2 \cdot m\right), \mathbb{R}\right),\; \operatorname{IsGaussianMeasurementCov}\left(sigmaM\right) \Leftrightarrow ((\operatorname{IsSymm}\left(sigmaM\right)) \land (\operatorname{PosSemidef}\left(\operatorname{Matrix.map}\left(sigmaM, \operatorname{Complex.ofReal}\right) + \operatorname{SMul.smul}\left(\operatorname{Complex.I}, \operatorname{Matrix.map}\left(\operatorname{Matrix.submatrix}\left(-\operatorname{Matrix.J}\left(\operatorname{Fin}\left(m\right), \mathbb{R}\right), (\lambda x:\operatorname{Fin}\left(2 \cdot m\right),\operatorname{if}\left(\operatorname{Fin.val}\left(x\right) \bmod 2 = 0, \operatorname{Sum.inl}\left((\operatorname{Fin.mk}\left(\operatorname{Nat.div}\left(\operatorname{Fin.val}\left(x\right), 2\right)\right):\operatorname{Fin}\left(m\right))\right), \operatorname{Sum.inr}\left((\operatorname{Fin.mk}\left(\operatorname{Nat.div}\left(\operatorname{Fin.val}\left(x\right), 2\right)\right):\operatorname{Fin}\left(m\right))\right)\right)), (\lambda x:\operatorname{Fin}\left(2 \cdot m\right),\operatorname{if}\left(\operatorname{Fin.val}\left(x\right) \bmod 2 = 0, \operatorname{Sum.inl}\left((\operatorname{Fin.mk}\left(\operatorname{Nat.div}\left(\operatorname{Fin.val}\left(x\right), 2\right)\right):\operatorname{Fin}\left(m\right))\right), \operatorname{Sum.inr}\left((\operatorname{Fin.mk}\left(\operatorname{Nat.div}\left(\operatorname{Fin.val}\left(x\right), 2\right)\right):\operatorname{Fin}\left(m\right))\right)\right))\right), \operatorname{Complex.ofReal}\right)\right)\right)))$$

*Formalization.* `D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation.IsGaussianMeasurementCov` (`✓ std3`).

*Citation.* M. F. B. Cenni; L. Lami; A. Acín; M. Mehboudi (2022). *Thermometry of Gaussian quantum systems using Gaussian measurements*. URL: <https://arxiv.org/abs/2110.02098v4>.

*Commentary.*

A real symmetric σᴹ is admissible when σᴹ + iΩ is positive semidefinite. The symplectic form is the interleaved-coordinate submatrix of -Matrix.J: even coordinates map to Sum.inl and odd coordinates to Sum.inr, both indexed by Nat.div(Fin.val(x),2). Nat.div is integer division; modulo is Nat.mod. Mapping this real form by Complex.ofReal equals the complex Matrix.J expression. Complex.I and SMul.smul give the complex scalar action.

**Definition 1.5 (Gaussian-measurement Fisher information).**

$$\forall n \in \mathbb{N},\; \forall sigma \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right),\; \forall d \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right),\; \forall sigmaM \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right),\; \operatorname{fisherC}\left(sigma, d, sigmaM\right) = 1/2 \cdot \operatorname{trace}\left(\left(\operatorname{inv}\left(sigma + sigmaM\right) \cdot d\right)^{2}\right)$$

*Formalization.* `D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation.fisherC` (`✓ std3`).

*Citation.* M. F. B. Cenni; L. Lami; A. Acín; M. Mehboudi (2022). *Thermometry of Gaussian quantum systems using Gaussian measurements*. URL: <https://arxiv.org/abs/2110.02098v4>.

*Commentary.*

With zero displacement, arXiv:2110.02098v4, p. 6 §3.2.2, Eq. (36) is Fᶜ(σ;σᴹ) = 1/2 tr[((σ + σᴹ)⁻¹ ∂Tσ)²].

**Definition 1.6 (Local measurement covariance).**

$$\forall m \in \mathbb{N},\; \forall M \in \operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; \forall i \in \operatorname{Fin}\left(2 \cdot m\right),\; \forall j \in \operatorname{Fin}\left(2 \cdot m\right),\; \operatorname{localCov}\left(M\right)\left(i, j\right) = \operatorname{if}\left((\operatorname{Fin.mk}\left(\operatorname{Nat.div}\left(\operatorname{Fin.val}\left(i\right), 2\right)\right):\operatorname{Fin}\left(m\right)) = (\operatorname{Fin.mk}\left(\operatorname{Nat.div}\left(\operatorname{Fin.val}\left(j\right), 2\right)\right):\operatorname{Fin}\left(m\right)), M\left((\operatorname{Fin.mk}\left(\operatorname{Nat.div}\left(\operatorname{Fin.val}\left(i\right), 2\right)\right):\operatorname{Fin}\left(m\right))\right)\left((\operatorname{Fin.mk}\left(\operatorname{Nat.mod}\left(\operatorname{Fin.val}\left(i\right), 2\right)\right):\operatorname{Fin}\left(2\right)), (\operatorname{Fin.mk}\left(\operatorname{Nat.mod}\left(\operatorname{Fin.val}\left(j\right), 2\right)\right):\operatorname{Fin}\left(2\right))\right), 0\right)$$

*Formalization.* `D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation.localCov` (`✓ std3`).

*Citation.* M. F. B. Cenni; L. Lami; A. Acín; M. Mehboudi (2022). *Thermometry of Gaussian quantum systems using Gaussian measurements*. URL: <https://arxiv.org/abs/2110.02098v4>.

*Commentary.*

localCov is the direct sum of the 2×2 blocks Mₖ. It uses the quotient i/2 for the mode and i modulo 2 for the within-mode coordinate.

**Definition 1.7 (Local Gaussian optimum).**

$$\forall m \in \mathbb{N},\; \forall omega \in \operatorname{Fin}\left(m\right) \to \mathbb{R},\; \forall T \in \mathbb{R},\; \operatorname{localFisher}\left(omega, T\right) = \operatorname{sSup}\left(\operatorname{Set.setOf}\left((\lambda f:\mathbb{R},\exists M \in \operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; (\forall k \in \operatorname{Fin}\left(m\right),\; \operatorname{IsGaussianMeasurementCov}\left(M\left(k\right)\right)) \land (f = \operatorname{fisherC}\left(\operatorname{thermalCov}\left(omega, T\right), \operatorname{thermalCovDeriv}\left(omega, T\right), \operatorname{localCov}\left(M\right)\right)))\right)\right)$$

*Formalization.* `D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation.localFisher` (`✓ std3`).

*Citation.* M. F. B. Cenni; L. Lami; A. Acín; M. Mehboudi (2022). *Thermometry of Gaussian quantum systems using Gaussian measurements*. URL: <https://arxiv.org/abs/2110.02098v4>.

*Commentary.*

The supremum ranges over all block-diagonal measurement covariances, with every 2×2 block symmetric and satisfying Mₖ+iJ ⪰ 0. It includes mixed as well as pure blocks and all rotations. At the refutation witness the local set is proved nonempty and bounded above by (153/400)(ln 3)².

**Definition 1.8 (The Eq. (47) conjecture).**

$$claim \Leftrightarrow (\forall m \in \mathbb{N},\; \forall omega \in \operatorname{Fin}\left(m\right) \to \mathbb{R},\; \forall T \in \mathbb{R},\; (\forall k \in \operatorname{Fin}\left(m\right),\; 0 < omega\left(k\right)) \Rightarrow ((0 < T) \Rightarrow (\forall sigmaM \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2 \cdot m\right), \operatorname{Fin}\left(2 \cdot m\right), \mathbb{R}\right),\; (\operatorname{IsGaussianMeasurementCov}\left(sigmaM\right)) \Rightarrow (\operatorname{fisherC}\left(\operatorname{thermalCov}\left(omega, T\right), \operatorname{thermalCovDeriv}\left(omega, T\right), sigmaM\right) \le \operatorname{localFisher}\left(omega, T\right)))))$$

*Formalization.* `D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation.claim` (`✓ std3`).

*Citation.* M. F. B. Cenni; L. Lami; A. Acín; M. Mehboudi (2022). *Thermometry of Gaussian quantum systems using Gaussian measurements*. URL: <https://arxiv.org/abs/2110.02098v4>.

*Commentary.*

Cenni et al., arXiv:2110.02098v4, §3.2, Eq. (47), compare, verbatim in TeX: "`{\cal F}^{\rm C}(\oplus_k {\bm \sigma}_{k}; {\bm \sigma}^M_{\max}) \overset{?}{=} {\cal F}^{\rm C}(\oplus_k {\bm \sigma}_{k}; \oplus_k{\bm \sigma}_{k,\max}^M)`" and state: "Based on these observations we conjecture this is generally true, however, a rigorous proof is missing currently." The claim retains the necessary upper-bound direction: every physical joint value is bounded by localFisher for every product thermal state with positive frequencies and positive temperature.

**Theorem 1.9 (The conjecture is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. F. B. Cenni; L. Lami; A. Acín; M. Mehboudi (2022). *Thermometry of Gaussian quantum systems using Gaussian measurements*. URL: <https://arxiv.org/abs/2110.02098v4>.

*Commentary.*

For two modes at T = 1 with frequencies (2 artanh(1/2), 4 artanh(1/2)), equivalently (ln 3, 2 ln 3), the thermal values are (2, 5/4). The explicit pure covariance generated by the symplectic matrix (1/5)[[13,0,12,0],[0,13,0,-12],[12,0,13,0],[0,-12,0,13]] gives Fᶜ/(artanh(1/2))² = 1493661/964324. The single-mode argument proves Loewner monotonicity for Fisher information, physical-to-pure domination, and rational bounds for every rotation at ν = 2 and ν = 5/4. Additivity bounds every physical local measurement by (153/100)(artanh(1/2))². Nonemptiness then bounds localFisher, strictly below the joint value; the rational gap is 114033/6027025 in those units.

## References

- Truth anchor: `D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation.IsGaussianMeasurementCov`
- Truth anchor: `D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation.claim`
- Truth anchor: `D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation.fisherC`
- Truth anchor: `D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation.localCov`
- Truth anchor: `D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation.localFisher`
- Truth anchor: `D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation.result`
- Truth anchor: `D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation.thermalCov`
- Truth anchor: `D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation.thermalCovDeriv`
- Truth anchor: `D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation.thermalNuDeriv`
- Dependency: [D5/S3/Observer/Fluctuation/ThermalCoefficientFloor](../Observer/Fluctuation/ThermalCoefficientFloor.md)
