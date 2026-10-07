# Isotropic even directional averages

## Abstract

A weighted-moment recurrence determines every isotropic directional even moment.

**Definition 1.1 (Rotate every momentum together).**

$$\forall N: \mathbb{N}, \forall R: \operatorname{LinearIsometryEquiv}\left(\mathbb{R}, \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right), \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)\right), \forall P: (\operatorname{Fin}\left(N\right)) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right), \operatorname{simultaneousRotation}\left(R, P\right) = (j: \operatorname{Fin}\left(N\right) \mapsto R\left(P\left(j\right)\right))$$

*Formalization.* `D5/S3/Quantum/KineticMoments/IsotropicAverage.simultaneousRotation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* P. Tolias; T. Dornheim; J. Vorberger (2025). *Kinetic contribution to the arbitrary order odd frequency moments of the dynamic structure factor*. DOI: [10.1002/ctpp.70090](https://doi.org/10.1002/ctpp.70090). URL: <https://arxiv.org/abs/2508.17810v1>.

*Commentary.*

A single real linear isometry is applied to every particle. Correlations between particles are preserved; independent rotations are not assumed.

**Definition 1.2 (Simultaneous SO(3) invariance).**

$$\forall N: \mathbb{N}, \forall nu: \operatorname{Measure}\left(((\operatorname{Fin}\left(N\right)) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right))\right), \operatorname{IsIsotropic}\left(nu\right) \Leftrightarrow (\forall R: \operatorname{LinearIsometryEquiv}\left(\mathbb{R}, \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right), \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)\right), (\operatorname{LinearMap}.\operatorname{det}\left(R.toLinearEquiv.toLinearMap\right) = 1) \Rightarrow \operatorname{MeasurePreserving}\left(\operatorname{simultaneousRotation}\left(R\right), nu, nu\right))$$

*Formalization.* `D5/S3/Quantum/KineticMoments/IsotropicAverage.IsIsotropic` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* P. Tolias; T. Dornheim; J. Vorberger (2025). *Kinetic contribution to the arbitrary order odd frequency moments of the dynamic structure factor*. DOI: [10.1002/ctpp.70090](https://doi.org/10.1002/ctpp.70090). URL: <https://arxiv.org/abs/2508.17810v1>.

*Commentary.*

Isotropy means that every determinant +1 linear isometry preserves the momentum-configuration measure. Reflections of determinant -1 are not assumed. Neither a probability normalization nor a moment bound is part of this predicate.

**Theorem 1.3 (Radial moment controls its directional moment).**

$$\forall N: \mathbb{N}, \forall nu: \operatorname{Measure}\left(((\operatorname{Fin}\left(N\right)) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right))\right), \forall j: \operatorname{Fin}\left(N\right), \forall i: \mathbb{N}, \forall q: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right), (\operatorname{Integrable}\left((P: (\operatorname{Fin}\left(N\right)) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right) \mapsto \Vert P\left(j\right)\Vert ^{2 \cdot i}), nu\right)) \Rightarrow \operatorname{Integrable}\left((P: (\operatorname{Fin}\left(N\right)) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right) \mapsto \langle q,P\left(j\right)\rangle ^{2 \cdot i}), nu\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/KineticMoments/IsotropicAverage.integrable_directional` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. Tolias; T. Dornheim; J. Vorberger (2025). *Kinetic contribution to the arbitrary order odd frequency moments of the dynamic structure factor*. DOI: [10.1002/ctpp.70090](https://doi.org/10.1002/ctpp.70090). URL: <https://arxiv.org/abs/2508.17810v1>.

*Commentary.*

The Cauchy-Schwarz inequality bounds |q·p_j|^(2i) by |q|^(2i)|p_j|^(2i). Radial integrability therefore suffices. This estimate controls the finite sums inside the odd moment integral.

**Theorem 1.4 (Exact isotropic directional average).**

$$\forall N: \mathbb{N}, \forall nu: \operatorname{Measure}\left(((\operatorname{Fin}\left(N\right)) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right))\right), \forall j: \operatorname{Fin}\left(N\right), \forall i: \mathbb{N}, \forall q: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right), (\operatorname{IsIsotropic}\left(nu\right)) \Rightarrow \left((\operatorname{Integrable}\left((P: (\operatorname{Fin}\left(N\right)) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right) \mapsto \Vert P\left(j\right)\Vert ^{2 \cdot i}), nu\right)) \Rightarrow \int_{P:(\operatorname{Fin}\left(N\right)) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)} \langle q,P\left(j\right)\rangle ^{2 \cdot i} \mathrm{d} nu = \frac{\Vert q\Vert ^{2 \cdot i} \cdot \int_{P:(\operatorname{Fin}\left(N\right)) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)} \Vert P\left(j\right)\Vert ^{2 \cdot i} \mathrm{d} nu}{2 \cdot (\operatorname{val}\left(i\right): \mathbb{R}) + 1}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/KineticMoments/IsotropicAverage.isotropic_average` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. Tolias; T. Dornheim; J. Vorberger (2025). *Kinetic contribution to the arbitrary order odd frequency moments of the dynamic structure factor*. DOI: [10.1002/ctpp.70090](https://doi.org/10.1002/ctpp.70090). URL: <https://arxiv.org/abs/2508.17810v1>.

*Commentary.*

The weighted directional moments are even, homogeneous and rotation invariant, so they depend only on |q|. Comparing the second coefficient in the polynomial for e_0+t e_l and summing all three coordinates gives the weighted recurrence. Induction yields the factor 1/(2i+1). The result applies to any isotropic measure with the stated integrable moment, including q=0 and i=0; it does not require a probability measure.

## References

- Truth anchor: `D5/S3/Quantum/KineticMoments/IsotropicAverage.IsIsotropic`
- Truth anchor: `D5/S3/Quantum/KineticMoments/IsotropicAverage.integrable_directional`
- Truth anchor: `D5/S3/Quantum/KineticMoments/IsotropicAverage.isotropic_average`
- Truth anchor: `D5/S3/Quantum/KineticMoments/IsotropicAverage.simultaneousRotation`
