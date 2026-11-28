# The actual lattice minimizers

## Abstract

Among planar lattices of any fixed positive covolume, the hexagonal lattice uniquely minimizes theta at every positive temperature, up to real orthogonal equivalence and the prescribed area scaling.

**Definition 1.1 (Orthogonal hexagonal images).**

$$\forall a \in \mathbb{C},\; \forall b \in \mathbb{C},\; \operatorname{IsHexagonalBasis}\left(a, b\right) \Leftrightarrow \left(\exists U \in \operatorname{LinearIsometryEquiv}\left(\mathbb{R}, \mathbb{C}, \mathbb{C}\right),\; \operatorname{range}\left((v:\mathbb{Z}\times\mathbb{Z} \mapsto (\operatorname{fst}\left(v\right):\mathbb{C}) \cdot a + (\operatorname{snd}\left(v\right):\mathbb{C}) \cdot b)\right) = \operatorname{image}\left(U, \operatorname{range}\left((v:\mathbb{Z}\times\mathbb{Z} \mapsto \operatorname{latticePoint}\left(\frac{1}{2}, \frac{\operatorname{sqrt}\left(3\right)}{2}, v\right))\right)\right)\right)$$

*Formalization.* `D5/S3/Fourier/ThetaLatticeMinimum.IsHexagonalBasis` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

The equality is equality of actual subsets of the complex plane, with the origin fixed. Both rotations and reflections are allowed.

**Theorem 1.2 (Squared-length scaling).**

$$\forall r \in \mathbb{R},\; \forall a \in \mathbb{C},\; \forall b \in \mathbb{C},\; \forall v \in \mathbb{Z}\times\mathbb{Z},\; \operatorname{normSq}\left((\operatorname{fst}\left(v\right):\mathbb{C}) \cdot \operatorname{smul}\left(r, a\right) + (\operatorname{snd}\left(v\right):\mathbb{C}) \cdot \operatorname{smul}\left(r, b\right)\right) = r^{2} \cdot \operatorname{normSq}\left((\operatorname{fst}\left(v\right):\mathbb{C}) \cdot a + (\operatorname{snd}\left(v\right):\mathbb{C}) \cdot b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ThetaLatticeMinimum.basis_normSq_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

A common real scaling of both basis vectors multiplies every squared length by the square of the scale. The identity holds for every real scale, including zero and negative scales.

**Theorem 1.3 (Theta scaling).**

$$\forall r \in \mathbb{R},\; \forall t \in \mathbb{R},\; \forall a \in \mathbb{C},\; \forall b \in \mathbb{C},\; \operatorname{basisTheta}\left(t, \operatorname{smul}\left(r, a\right), \operatorname{smul}\left(r, b\right)\right) = \operatorname{basisTheta}\left(t \cdot r^{2}, a, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ThetaLatticeMinimum.basisTheta_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

Apply the squared-length scaling identity to every Gaussian term. Scaling both basis vectors by r replaces temperature t by t times r squared.

**Theorem 1.4 (Unit-area normalization).**

$$\forall a \in \mathbb{C},\; \forall b \in \mathbb{C},\; \forall A \in \mathbb{R},\; 0 < A \Rightarrow \left(\left|\operatorname{re}\left(a\right) \cdot \operatorname{im}\left(b\right) - \operatorname{im}\left(a\right) \cdot \operatorname{re}\left(b\right)\right| = A \Rightarrow \left|\operatorname{re}\left(\operatorname{smul}\left(\frac{1}{\operatorname{sqrt}\left(A\right)}, a\right)\right) \cdot \operatorname{im}\left(\operatorname{smul}\left(\frac{1}{\operatorname{sqrt}\left(A\right)}, b\right)\right) - \operatorname{im}\left(\operatorname{smul}\left(\frac{1}{\operatorname{sqrt}\left(A\right)}, a\right)\right) \cdot \operatorname{re}\left(\operatorname{smul}\left(\frac{1}{\operatorname{sqrt}\left(A\right)}, b\right)\right)\right| = 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ThetaLatticeMinimum.basis_normalized_area` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

Scaling both basis vectors by the reciprocal square root of the positive covolume multiplies the determinant by its reciprocal. Its absolute value therefore becomes one, for either orientation.

**Theorem 1.5 (Montgomery's lattice minimum).**

$$\forall a \in \mathbb{C},\; \forall b \in \mathbb{C},\; \forall A \in \mathbb{R},\; \forall t \in \mathbb{R},\; 0 < A \Rightarrow \left(\left|\operatorname{re}\left(a\right) \cdot \operatorname{im}\left(b\right) - \operatorname{im}\left(a\right) \cdot \operatorname{re}\left(b\right)\right| = A \Rightarrow \left(0 < t \Rightarrow \left(\operatorname{F}\left(A \cdot t, \frac{1}{2}, \frac{\operatorname{sqrt}\left(3\right)}{2}\right) \le \operatorname{basisTheta}\left(t, a, b\right) \land \left(\operatorname{basisTheta}\left(t, a, b\right) = \operatorname{F}\left(A \cdot t, \frac{1}{2}, \frac{\operatorname{sqrt}\left(3\right)}{2}\right) \Leftrightarrow \operatorname{IsHexagonalBasis}\left(\operatorname{smul}\left(\frac{1}{\operatorname{sqrt}\left(A\right)}, a\right), \operatorname{smul}\left(\frac{1}{\operatorname{sqrt}\left(A\right)}, b\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ThetaLatticeMinimum.basis_theta_minimum_isometry` (`✓ std3`). ∎

*Citation.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

Normalize both basis vectors by the reciprocal square root of their positive covolume A. The normalized basis has area one, and scaling its squared lengths changes the temperature to A times t. The reduced theta minimum and pointwise orthogonal realization give the lower bound and classify equality exactly by the normalized lattice being an orthogonal hexagonal image.

## References

- Truth anchor: `D5/S3/Fourier/ThetaLatticeMinimum.IsHexagonalBasis`
- Truth anchor: `D5/S3/Fourier/ThetaLatticeMinimum.basisTheta_scale`
- Truth anchor: `D5/S3/Fourier/ThetaLatticeMinimum.basis_normSq_scale`
- Truth anchor: `D5/S3/Fourier/ThetaLatticeMinimum.basis_normalized_area`
- Truth anchor: `D5/S3/Fourier/ThetaLatticeMinimum.basis_theta_minimum_isometry`
- Dependency: [D5/S3/Fourier/HexagonalThetaMinimum](HexagonalThetaMinimum.md)
- Dependency: [D5/S3/Fourier/PlanarThetaFoundation](PlanarThetaFoundation.md)
