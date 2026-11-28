# The ADM metric, Hamiltonian and time-symmetric conformal data

## Abstract

The ADM metric, Hamiltonian and time-symmetric conformal data.

The lapse and shift describe a four-dimensional metric in a frame adapted to a spatial slice. In an orthonormal spatial frame the canonical momentum has one trace direction with negative kinetic form and five traceless directions with positive kinetic form. Time-symmetric isotropic data give explicit mass and area identities.

**Definition 1.1 (Shift matrix).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.admShiftMatrix`

*Formalization.* `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.admShiftMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

The unit lower triangular matrix adds the shift multiplied by the time component to the spatial components.

**Definition 1.2 (Spacetime metric).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.admMetric`

*Formalization.* `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.admMetric` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

The block form records the spatial metric, its pairings with the shift and the lapse term in the time entry.

**Definition 1.3 (Inverse spacetime metric).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.admInvMetric`

*Formalization.* `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.admInvMetric` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

The spatial inverse is corrected by the shift outer product divided by the squared lapse. The time entry is minus the reciprocal squared lapse.

**Theorem 1.4 (Lapse and shift congruence).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.admMetric_congruence_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.admMetric_congruence_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

The metric is the congruence of the block diagonal matrix with time entry equal to minus the lapse squared and spatial block equal to the spatial metric. The congruence uses the lower triangular shift matrix.

**Theorem 1.5 (Two-sided inverse).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.admMetric_mul_inv`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.admMetric_mul_inv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

A nonzero lapse and a two-sided spatial inverse give a two-sided inverse of the spacetime metric. Its mixed blocks are the shift components divided by the lapse squared.

**Theorem 1.6 (Determinant and volume).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.admMetric_det_and_volume`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.admMetric_det_and_volume` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

The determinant is minus the lapse squared times the spatial determinant. The square root of its negative is the positive lapse times the square root of the nonnegative spatial determinant.

**Definition 1.7 (Normal vector components).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.nUp`

*Formalization.* `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.nUp` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

The contravariant components are the reciprocal lapse and the negative shift divided by the lapse.

**Definition 1.8 (Spatial coordinate basis).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.eSpatial`

*Formalization.* `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.eSpatial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

A spatial coordinate vector has zero time component and one selected spatial component equal to one.

**Theorem 1.9 (Normal to the spatial slice).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.adm_unit_timelike_normal`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.adm_unit_timelike_normal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

For nonzero lapse the normal has time component equal to the reciprocal lapse and spatial components equal to the negative shift divided by the lapse. Lowering its index gives a covector with time component equal to the negative lapse and vanishing spatial components. Its squared length is minus one and its pairing with every spatial basis vector vanishes.

**Theorem 1.10 (Lorentzian signature).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.adm_lorentzian_signature`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.adm_lorentzian_signature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

For positive lapse and symmetric positive definite spatial metric the quadratic form is the shifted spatial quadratic form minus the square of the lapse times the time component. Symmetry, negativity on the normal and positivity on the full spatial hyperplane determine the signature.

**Definition 1.11 (Canonical momentum).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.admMomentum`

*Formalization.* `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.admMomentum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

Subtract the curvature trace times the identity and multiply by the volume factor.

**Definition 1.12 (Extrinsic curvature from momentum).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.admExtrinsicFromMomentum`

*Formalization.* `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.admExtrinsicFromMomentum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

Subtract half the momentum trace times the identity and divide by the volume factor.

**Definition 1.13 (DeWitt kinetic form).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.dewittKinetic`

*Formalization.* `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.dewittKinetic` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

Take the trace of the momentum square and subtract half the square of its trace.

**Theorem 1.14 (Momentum and extrinsic curvature).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.adm_legendre_transform_involution`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.adm_legendre_transform_involution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

In three spatial dimensions the forward and inverse trace-adjusted maps are mutual inverses at nonzero volume factor. Taking the trace of the momentum gives minus twice the volume factor times the curvature trace. Substitution into the quadratic kinetic form gives the inverse square of the volume factor and the momentum trace coefficient one half.

**Theorem 1.15 (Conformal and shear directions).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.dewitt_supermetric_lorentzian_signature`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.dewitt_supermetric_lorentzian_signature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

The trace part contributes minus one sixth of the squared trace. The traceless part contributes the trace of its square, strictly positive for nonzero symmetric shear. The projection remains symmetric. Two diagonal and three off-diagonal entries uniquely parametrize that shear. A nonzero scalar matrix has kinetic value minus three halves times its scalar coefficient squared.

**Theorem 1.16 (Friedmann constraint).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.adm_hamiltonian_constraint_reproduces_friedmann`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.adm_hamiltonian_constraint_reproduces_friedmann` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

At positive scale factor, raising one index of the extrinsic curvature gives the Hubble rate times the identity. The trace combination reduces to minus six times the Hubble rate squared. With spatial curvature six times the curvature parameter divided by the scale factor squared, the Hamiltonian constraint is equivalent to the first Friedmann equation.

**Definition 1.17 (Radial Laplacian).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.radialLaplacian`

*Formalization.* `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.radialLaplacian` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

Add the second radial derivative to twice the first radial derivative divided by radius.

**Definition 1.18 (Conformal scalar curvature).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.conformalScalarCurvature`

*Formalization.* `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.conformalScalarCurvature` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

Multiply the radial Laplacian by minus eight times the inverse fifth power of the conformal factor.

**Definition 1.19 (Schwarzschild conformal factor).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.schwPsi`

*Formalization.* `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.schwPsi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

Add one to the mass divided by twice the isotropic radius.

**Theorem 1.20 (The isotropic vacuum constraint).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.lichnerowicz_radial_harmonic_vanishing`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.lichnerowicz_radial_harmonic_vanishing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

On the positive radial half-line, twice differentiating the Schwarzschild conformal factor gives the opposite of twice its first derivative divided by radius. The radial Laplacian and the modeled conformal scalar curvature both vanish.

**Definition 1.21 (Areal radius).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.isotropicArealRadius`

*Formalization.* `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.isotropicArealRadius` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

Multiply the isotropic radius by the square of the conformal factor.

**Definition 1.22 (Isotropic radial inversion).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.isotropicInversion`

*Formalization.* `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.isotropicInversion` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

Divide the squared mass by four times the isotropic radius.

**Theorem 1.23 (Isotropic inversion and the throat).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.isotropic_schwarzschild_throat_and_inversion_isometry`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.isotropic_schwarzschild_throat_and_inversion_isometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

For positive mass and radius, inversion by one quarter of the squared mass preserves the areal radius and pulls back the radial metric factor. The map is its own inverse and exchanges the intervals on either side of the throat. The areal radius has unique minimum twice the mass at isotropic radius equal to half the mass. This matches the horizon radius in the Kruskal bridge.

**Definition 1.24 (Conformal surface flux).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.conformalADMMass`

*Formalization.* `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.conformalADMMass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

Multiply the first radial derivative by minus twice the square of the radius and the cube of the conformal factor.

**Definition 1.25 (Komar mass expression).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.komarSchwarzschildMass`

*Formalization.* `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.komarSchwarzschildMass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

Multiply the radial flux density by the sphere area and divide by four pi.

**Theorem 1.26 (Schwarzschild surface masses).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.schwarzschild_adm_mass_limit_and_komar_invariance`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.schwarzschild_adm_mass_limit_and_komar_invariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

The finite-radius conformal flux is the mass times the cube of the conformal factor and converges to the mass at infinity. The Komar surface expression equals the mass at every positive areal radius.

**Definition 1.27 (Brill-Lindquist conformal factor).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.blPsi`

*Formalization.* `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.blPsi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

Add one to the sum of the mass parameters divided by twice the distance to their respective centers.

**Definition 1.28 (Brill-Lindquist outer mass).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.blADMMass`

*Formalization.* `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.blADMMass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

Sum the mass parameters of all centers.

**Definition 1.29 (Brill-Lindquist inner mass).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.blBareMass`

*Formalization.* `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.blBareMass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

Multiply the selected mass parameter by the conformal factor from all the other centers evaluated at the selected center.

**Theorem 1.30 (Brill-Lindquist flux and binding).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.brill_lindquist_harmonic_positive_mass_and_binding_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.brill_lindquist_harmonic_positive_mass_and_binding_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

The conformal factor is harmonic off the punctures. Its normalized radial flux tends on every unit ray to the sum of the mass parameters, which is positive for nonempty data with positive masses. The binding energy is minus one half of the sum over ordered distinct pairs of their mass product divided by distance. It is strictly negative if there are at least two centers, the centers are pairwise distinct and all masses are positive.

**Theorem 1.31 (Schwarzschild equality case).**

Lean statement: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.riemannian_penrose_inequality_schwarzschild_saturation`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.riemannian_penrose_inequality_schwarzschild_saturation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Richard Arnowitt, Stanley Deser, and Charles W. Misner (2008). *The dynamics of general relativity*. DOI: [10.1007/s10714-008-0661-1](https://doi.org/10.1007/s10714-008-0661-1). URL: <https://arxiv.org/abs/gr-qc/0405109>.

*Commentary.*

For positive mass, the throat area is sixteen pi times the square of the mass, and the square root of the area divided by sixteen pi equals the mass. At zero Kruskal time the throat relation forces the spatial Kruskal coordinate to vanish.

## References

- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.admExtrinsicFromMomentum`
- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.admInvMetric`
- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.admMetric`
- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.admMetric_congruence_factorization`
- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.admMetric_det_and_volume`
- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.admMetric_mul_inv`
- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.admMomentum`
- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.admShiftMatrix`
- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.adm_hamiltonian_constraint_reproduces_friedmann`
- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.adm_legendre_transform_involution`
- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.adm_lorentzian_signature`
- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.adm_unit_timelike_normal`
- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.blADMMass`
- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.blBareMass`
- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.blPsi`
- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.brill_lindquist_harmonic_positive_mass_and_binding_energy`
- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.conformalADMMass`
- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.conformalScalarCurvature`
- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.dewittKinetic`
- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.dewitt_supermetric_lorentzian_signature`
- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.eSpatial`
- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.isotropicArealRadius`
- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.isotropicInversion`
- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.isotropic_schwarzschild_throat_and_inversion_isometry`
- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.komarSchwarzschildMass`
- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.lichnerowicz_radial_harmonic_vanishing`
- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.nUp`
- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.radialLaplacian`
- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.riemannian_penrose_inequality_schwarzschild_saturation`
- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.schwPsi`
- Truth anchor: `D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D.schwarzschild_adm_mass_limit_and_komar_invariance`
- Dependency: [D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D](FLRWCosmologyFriedmann4D.md)
- Dependency: [D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D](PenroseCarterCausalCompactification4D.md)
- Dependency: [D5/S3/Geometry/Lorentz/PenroseHawkingSingularityBPS4D](PenroseHawkingSingularityBPS4D.md)
