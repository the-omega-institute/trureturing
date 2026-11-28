# Planar theta geometry and orthogonal realization

## Abstract

The normalized binary form has a summable Gaussian series, reciprocal-temperature duality and additive lattice reduction. Preserving its quadratic form gives a pointwise orthogonal lattice realization, including the degenerate zero-height case.

**Definition 1.1 (Binary form).**

$$\forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; \forall v \in \mathbb{Z}\times\mathbb{Z},\; \operatorname{Q}\left(x, y, v\right) = \frac{\left((\operatorname{fst}\left(v\right):\mathbb{R}) + (\operatorname{snd}\left(v\right):\mathbb{R}) \cdot x\right)^{2}}{y} + y \cdot (\operatorname{snd}\left(v\right):\mathbb{R})^{2}$$

*Formalization.* `D5/S3/Fourier/PlanarThetaFoundation.Q` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

For y > 0, the form is the squared length in the normalized complex lattice.

**Definition 1.2 (Planar theta series).**

$$\forall t \in \mathbb{R},\; \forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; \operatorname{F}\left(t, x, y\right) = \operatorname{tsum}\left((v:\mathbb{Z}\times\mathbb{Z} \mapsto \operatorname{exp}\left(-\left(\pi \cdot t \cdot \operatorname{Q}\left(x, y, v\right)\right)\right))\right)$$

*Formalization.* `D5/S3/Fourier/PlanarThetaFoundation.F` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

Integer pairs index the Gaussian series, including the zero vector.

**Theorem 1.3 (Uniform coercivity).**

$$\forall M \in \mathbb{R},\; \forall l \in \mathbb{R},\; \forall u \in \mathbb{R},\; \forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; 0 < l \Rightarrow \left(\left|x\right| \le M \Rightarrow \left(l \le y \Rightarrow \left(y \le u \Rightarrow \left(\forall v \in \mathbb{Z}\times\mathbb{Z},\; (\operatorname{fst}\left(v\right):\mathbb{R})^{2} + (\operatorname{snd}\left(v\right):\mathbb{R})^{2} \le \operatorname{max}\left(2 \cdot u, \frac{2 \cdot M^{2} + 1}{l}\right) \cdot \operatorname{Q}\left(x, y, v\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/PlanarThetaFoundation.quadratic_control` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

The inequality m squared plus n squared is bounded by twice the shifted square plus (twice x squared plus one) times n squared. Taking the maximum of the two coefficients gives one bound on each height rectangle.

**Theorem 1.4 (Absolute convergence).**

$$\forall t \in \mathbb{R},\; \forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; 0 < t \Rightarrow \left(0 < y \Rightarrow \operatorname{Summable}\left((v:\mathbb{Z}\times\mathbb{Z} \mapsto \operatorname{exp}\left(-\left(\pi \cdot t \cdot \operatorname{Q}\left(x, y, v\right)\right)\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/PlanarThetaFoundation.summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

The Gram matrix is positive definite, with determinant one. Matrix Gaussian summability applies after identifying two coordinates with an integer pair.

**Theorem 1.5 (Shear derivative).**

$$\forall t \in \mathbb{R},\; \forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; 0 < t \Rightarrow \left(0 < y \Rightarrow \operatorname{HasDerivAt}\left((a:\mathbb{R} \mapsto \operatorname{F}\left(t, a, y\right)), \operatorname{tsum}\left((v:\mathbb{Z}\times\mathbb{Z} \mapsto -\left(\pi \cdot t \cdot \frac{2 \cdot (\operatorname{snd}\left(v\right):\mathbb{R}) \cdot \left((\operatorname{fst}\left(v\right):\mathbb{R}) + (\operatorname{snd}\left(v\right):\mathbb{R}) \cdot x\right)}{y}\right) \cdot \operatorname{exp}\left(-\left(\pi \cdot t \cdot \operatorname{Q}\left(x, y, v\right)\right)\right))\right), x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/PlanarThetaFoundation.hasDerivAt_shear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

On a bounded shear interval, the differentiated summands are bounded by a constant times the squared coordinate size times a fixed Gaussian. The one-dimensional polynomial Gaussian bounds give summability.

**Theorem 1.6 (Height derivative).**

$$\forall t \in \mathbb{R},\; \forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; 0 < t \Rightarrow \left(0 < y \Rightarrow \operatorname{HasDerivAt}\left((b:\mathbb{R} \mapsto \operatorname{F}\left(t, x, b\right)), \operatorname{tsum}\left((v:\mathbb{Z}\times\mathbb{Z} \mapsto -\left(\pi \cdot t \cdot \left((\operatorname{snd}\left(v\right):\mathbb{R})^{2} - \frac{\left((\operatorname{fst}\left(v\right):\mathbb{R}) + (\operatorname{snd}\left(v\right):\mathbb{R}) \cdot x\right)^{2}}{y^{2}}\right)\right) \cdot \operatorname{exp}\left(-\left(\pi \cdot t \cdot \operatorname{Q}\left(x, y, v\right)\right)\right))\right), y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/PlanarThetaFoundation.hasDerivAt_height` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

Restricting height to an interval bounded away from zero controls the reciprocal powers. A summable uniform derivative bound permits differentiation.

**Theorem 1.7 (Second height derivative).**

$$\forall t \in \mathbb{R},\; \forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; 0 < t \Rightarrow \left(0 < y \Rightarrow \operatorname{HasDerivAt}\left((b:\mathbb{R} \mapsto \operatorname{deriv}\left((z:\mathbb{R} \mapsto \operatorname{F}\left(t, x, z\right)), b\right)), \operatorname{tsum}\left((v:\mathbb{Z}\times\mathbb{Z} \mapsto \left(\left(\pi \cdot t\right)^{2} \cdot \left((\operatorname{snd}\left(v\right):\mathbb{R})^{2} - \frac{\left((\operatorname{fst}\left(v\right):\mathbb{R}) + (\operatorname{snd}\left(v\right):\mathbb{R}) \cdot x\right)^{2}}{y^{2}}\right)^{2} - \pi \cdot t \cdot \frac{2 \cdot \left((\operatorname{fst}\left(v\right):\mathbb{R}) + (\operatorname{snd}\left(v\right):\mathbb{R}) \cdot x\right)^{2}}{y^{3}}\right) \cdot \operatorname{exp}\left(-\left(\pi \cdot t \cdot \operatorname{Q}\left(x, y, v\right)\right)\right))\right), y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/PlanarThetaFoundation.hasDerivAt_height_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

The second Gaussian derivative has a quadratic square term and a second-form derivative term. Fourth Gaussian moments dominate the former and second moments dominate the latter.

**Theorem 1.8 (Reciprocal temperature).**

$$\forall t \in \mathbb{R},\; \forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; 0 < t \Rightarrow \left(0 < y \Rightarrow \operatorname{F}\left(t, x, y\right) = t^{-1} \cdot \operatorname{F}\left(t^{-1}, x, y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/PlanarThetaFoundation.temperature_duality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

Coordinate Poisson summation uses the inverse Gram matrix. In dimension two its form is the original form after an integer quarter-turn. The unit determinant and dimension two reduce the factor to reciprocal t.

**Definition 1.9 (Normalized lattice points).**

$$\forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; \forall v \in \mathbb{Z}\times\mathbb{Z},\; \operatorname{latticePoint}\left(x, y, v\right) = \operatorname{ComplexMk}\left(\frac{(\operatorname{fst}\left(v\right):\mathbb{R}) + (\operatorname{snd}\left(v\right):\mathbb{R}) \cdot x}{\operatorname{sqrt}\left(y\right)}, \operatorname{sqrt}\left(y\right) \cdot (\operatorname{snd}\left(v\right):\mathbb{R})\right)$$

*Formalization.* `D5/S3/Fourier/PlanarThetaFoundation.latticePoint` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

The two real coordinates use reciprocal square-root and square-root scaling.

**Theorem 1.10 (Lengths and injectivity).**

$$\forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; 0 < y \Rightarrow \left(\operatorname{Injective}\left((v:\mathbb{Z}\times\mathbb{Z} \mapsto \operatorname{latticePoint}\left(x, y, v\right))\right) \land \left(\forall v \in \mathbb{Z}\times\mathbb{Z},\; \operatorname{normSq}\left(\operatorname{latticePoint}\left(x, y, v\right)\right) = \operatorname{Q}\left(x, y, v\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/PlanarThetaFoundation.lattice_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

The imaginary coordinate recovers the second integer; the real coordinate then recovers the first. The square-root identity gives the squared length.

**Definition 1.11 (Theta in arbitrary basis coordinates).**

$$\forall t \in \mathbb{R},\; \forall a \in \mathbb{C},\; \forall b \in \mathbb{C},\; \operatorname{basisTheta}\left(t, a, b\right) = \operatorname{tsum}\left((v:\mathbb{Z}\times\mathbb{Z} \mapsto \operatorname{exp}\left(-\left(\pi \cdot t \cdot \operatorname{normSq}\left((\operatorname{fst}\left(v\right):\mathbb{C}) \cdot a + (\operatorname{snd}\left(v\right):\mathbb{C}) \cdot b\right)\right)\right))\right)$$

*Formalization.* `D5/S3/Fourier/PlanarThetaFoundation.basisTheta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

Complex basis vectors give the Euclidean lengths of integer combinations.

**Theorem 1.12 (Geometric basis reduction).**

$$\forall a \in \mathbb{C},\; \forall b \in \mathbb{C},\; \left|\operatorname{re}\left(a\right) \cdot \operatorname{im}\left(b\right) - \operatorname{im}\left(a\right) \cdot \operatorname{re}\left(b\right)\right| = 1 \Rightarrow \left(\exists x \in \mathbb{R},\; \exists y \in \mathbb{R},\; 0 \le x \land \left(x \le \frac{1}{2} \land \left(0 < y \land \left(1 \le x^{2} + y^{2} \land \left(\frac{\operatorname{sqrt}\left(3\right)}{2} \le y \land \left(\exists e \in \operatorname{AddEquiv}\left(\mathbb{Z}\times\mathbb{Z}, \mathbb{Z}\times\mathbb{Z}\right),\; \forall v \in \mathbb{Z}\times\mathbb{Z},\; \operatorname{normSq}\left((\operatorname{fst}\left(v\right):\mathbb{C}) \cdot a + (\operatorname{snd}\left(v\right):\mathbb{C}) \cdot b\right) = \operatorname{Q}\left(x, y, \operatorname{apply}\left(e, v\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/PlanarThetaFoundation.basis_reduction_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

The modular coordinate change is an additive equivalence of integer pairs. Its inverse, followed by the possible shear reflection, identifies the original quadratic form with a reduced one at every integer coordinate. For an arbitrary unit-area basis, the squared length identity then retains this same additive reindexing. Thus the reduction preserves both lengths and lattice addition.

**Theorem 1.13 (Pointwise lattice isometry).**

$$\forall a \in \mathbb{C},\; \forall b \in \mathbb{C},\; \forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; \forall e \in \operatorname{AddEquiv}\left(\mathbb{Z}\times\mathbb{Z}, \mathbb{Z}\times\mathbb{Z}\right),\; \left(\forall v \in \mathbb{Z}\times\mathbb{Z},\; \operatorname{normSq}\left((\operatorname{fst}\left(v\right):\mathbb{C}) \cdot a + (\operatorname{snd}\left(v\right):\mathbb{C}) \cdot b\right) = \operatorname{Q}\left(x, y, \operatorname{apply}\left(e, v\right)\right)\right) \Rightarrow \left(\exists U \in \operatorname{LinearIsometryEquiv}\left(\mathbb{R}, \mathbb{C}, \mathbb{C}\right),\; \forall v \in \mathbb{Z}\times\mathbb{Z},\; \operatorname{apply}\left(U, (\operatorname{fst}\left(v\right):\mathbb{C}) \cdot a + (\operatorname{snd}\left(v\right):\mathbb{C}) \cdot b\right) = \operatorname{latticePoint}\left(x, y, \operatorname{apply}\left(e, v\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/PlanarThetaFoundation.basis_isometry_of_quadratic_reindex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

Take the original lattice vectors whose new coordinates are one zero and zero one. Additivity identifies every integer combination of these vectors. Their squared lengths and the squared length of their sum determine the full Gram matrix. This matrix agrees with the normalized shear-height basis. The resulting real-linear map preserves the norm on the entire plane. Its injectivity and finite dimension give surjectivity, hence a linear isometric equivalence. Inverting this map gives the asserted pointwise identification, including either orientation. At zero height both basis vectors vanish; negative height is incompatible with the quadratic identity.

## References

- Truth anchor: `D5/S3/Fourier/PlanarThetaFoundation.F`
- Truth anchor: `D5/S3/Fourier/PlanarThetaFoundation.Q`
- Truth anchor: `D5/S3/Fourier/PlanarThetaFoundation.basisTheta`
- Truth anchor: `D5/S3/Fourier/PlanarThetaFoundation.basis_isometry_of_quadratic_reindex`
- Truth anchor: `D5/S3/Fourier/PlanarThetaFoundation.basis_reduction_geometry`
- Truth anchor: `D5/S3/Fourier/PlanarThetaFoundation.hasDerivAt_height`
- Truth anchor: `D5/S3/Fourier/PlanarThetaFoundation.hasDerivAt_height_deriv`
- Truth anchor: `D5/S3/Fourier/PlanarThetaFoundation.hasDerivAt_shear`
- Truth anchor: `D5/S3/Fourier/PlanarThetaFoundation.latticePoint`
- Truth anchor: `D5/S3/Fourier/PlanarThetaFoundation.lattice_geometry`
- Truth anchor: `D5/S3/Fourier/PlanarThetaFoundation.quadratic_control`
- Truth anchor: `D5/S3/Fourier/PlanarThetaFoundation.summable`
- Truth anchor: `D5/S3/Fourier/PlanarThetaFoundation.temperature_duality`
- Dependency: [D5/S3/Fourier/MatrixGaussianTheta](MatrixGaussianTheta.md)
