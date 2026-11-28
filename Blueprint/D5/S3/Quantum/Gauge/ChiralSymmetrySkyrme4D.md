# Two-flavor chiral symmetry, pion masses and Skyrme energy

## Abstract

The two-flavor chiral orbit, the tree-level pion mass and anomaly factor, and Skyrme energy bounds.

The left and right SU(2) factors act on the chiral field by multiplication on the left and inverse multiplication on the right. The chiral potential is the real trace of the diagonal quark mass matrix times the field, weighted by minus the mass parameter times the squared decay constant.

**Theorem 1.1 (Diagonal vacuum stabilizer).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.chiral_vacuum_stabilizer_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.chiral_vacuum_stabilizer_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pair of left and right group elements fixes the identity field exactly when its two entries are equal.

**Theorem 1.2 (Chiral vacuum orbit).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.chiral_orbit_transitive`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.chiral_orbit_transitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every determinant-one unitary two-by-two matrix is the image of the identity under some left and right group elements.

**Definition 1.3 (Cosets of the diagonal subgroup).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.chiralCosetEquiv`

*Formalization.* `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.chiralCosetEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The equivalence from left cosets of the diagonal subgroup sends the coset of a left and right pair to its action on the identity. The inverse sends a field to the coset of the pair with that field on the left and the identity on the right.

**Definition 1.4 (Three-sphere coordinates for SU(2)).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.su2SphereCoordinates`

*Formalization.* `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.su2SphereCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real part of the upper-left entry, the imaginary and real parts of the upper-right entry, and the imaginary part of the upper-left entry give the four real coordinates in that order. The map and its continuous inverse identify SU(2) with the unit sphere in real four-space.

**Theorem 1.5 (Matrix exponential of the pion field).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.chiralField_eq_exp`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.chiralField_eq_exp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real decay parameter and pion triple, the closed field formula equals the matrix exponential of the Pauli matrix of the triple scaled by the imaginary unit divided by the decay parameter. At zero decay parameter both sides are the identity under totalized division.

**Theorem 1.6 (Pion field in SU(2)).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.chiralField_mem_su2`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.chiralField_mem_su2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At nonzero decay constant the cosine term and the sinc-weighted Pauli term give a unitary matrix of determinant one for every real pion triple. The sinc function is the sine divided by its argument, with value one at zero.

**Theorem 1.7 (Pion field at the origin).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.chiralField_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.chiralField_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero pion triple gives the identity matrix.

**Theorem 1.8 (Canonical quadratic kinetic normalization).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.chiral_kinetic_quadratic_normalization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.chiral_kinetic_quadratic_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive decay constant and any pion direction, the directional field curve is differentiable at zero. Its derivative is the Pauli matrix of the direction times the imaginary unit divided by the decay constant. The real trace of its Hermitian adjoint times itself, weighted by one quarter of the squared decay constant, is half the squared Euclidean length of the direction.

**Theorem 1.9 (Unique minimum of the mass potential).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.chiralPotential_global_min_at_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.chiralPotential_global_min_at_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive mass parameter, decay constant and both quark masses, the chiral potential over SU(2) is minimized at the identity. Equality with the minimum holds exactly at the identity matrix.

**Theorem 1.10 (Directional Hessian of the pion potential).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.gmor_exact_hessian`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.gmor_exact_hessian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Murray Gell-Mann, R. J. Oakes, and B. Renner (1968). *Behavior of Current Divergences under SU(3) × SU(3)*. DOI: [10.1103/PhysRev.175.2195](https://doi.org/10.1103/PhysRev.175.2195). URL: <https://doi.org/10.1103/PhysRev.175.2195>.

*Commentary.*

At positive decay constant the second derivative at zero along any pion line is the mass parameter times the quark mass sum times the squared Euclidean length of the direction.

**Theorem 1.11 (Common pion mass and chiral limit).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.gmor_pion_mass_relation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.gmor_pion_mass_relation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Murray Gell-Mann, R. J. Oakes, and B. Renner (1968). *Behavior of Current Divergences under SU(3) × SU(3)*. DOI: [10.1103/PhysRev.175.2195](https://doi.org/10.1103/PhysRev.175.2195). URL: <https://doi.org/10.1103/PhysRev.175.2195>.

*Commentary.*

At positive decay constant the common squared mass is the mass parameter times the quark mass sum. Multiplying it by the squared decay constant gives the quark mass sum times the condensate parameter. The three coordinate directions have this same curvature. With fixed mass parameter, the squared mass tends to zero as the quark mass sum tends to zero.

**Theorem 1.12 (Cancellation of the color factor).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.abj_anomaly_free_general_Nc`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.abj_anomaly_free_general_Nc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each nonzero real color parameter, divide its sum with one by twice the color parameter to obtain the up charge. Divide one minus the color parameter by the same denominator to obtain the down charge. These charges yield anomaly factor one.

**Theorem 1.13 (Color dependence at fixed charges).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.abj_fixed_charges_color_test`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.abj_fixed_charges_color_test` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At fixed charges two thirds and minus one third the anomaly factor is the color parameter divided by three. The factor is one at three colors. For positive decay constant the normalized two-photon width at three colors is nine times its value at one color.

**Theorem 1.14 (Pointwise Skyrme energy bound).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.faddeev_bogomolny_skyrme_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.faddeev_bogomolny_skyrme_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real strain triple, the quadratic energy, obtained by summing strain squares, plus the quartic energy, obtained by summing products of distinct strain squares over unordered pairs, is at least six times the absolute product of the three strains.

**Theorem 1.15 (Equality in the pointwise bound).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.faddeev_bogomolny_saturation_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.faddeev_bogomolny_saturation_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality holds exactly when all three strains vanish or all three have absolute value one.

**Theorem 1.16 (Pure sigma energy under spatial scaling).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.derrick_no_pure_sigma_soliton`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.derrick_no_pure_sigma_soliton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With positive quadratic energy and zero quartic energy, the energy is strictly decreasing on positive scales, tends to zero at positive infinity, and has no minimum on that interval.

**Theorem 1.17 (Unique Skyrme scaling minimum).**

Lean statement: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.derrick_skyrme_virial_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.derrick_skyrme_virial_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When both energy coefficients are positive, the reciprocal-scale quadratic term and the linear-scale quartic term coincide at the square root of their coefficient ratio. This positive scale is the unique strict global minimizer, with energy twice the square root of the coefficient product.

## References

- Truth anchor: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.abj_anomaly_free_general_Nc`
- Truth anchor: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.abj_fixed_charges_color_test`
- Truth anchor: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.chiralCosetEquiv`
- Truth anchor: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.chiralField_eq_exp`
- Truth anchor: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.chiralField_mem_su2`
- Truth anchor: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.chiralField_zero`
- Truth anchor: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.chiralPotential_global_min_at_one`
- Truth anchor: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.chiral_kinetic_quadratic_normalization`
- Truth anchor: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.chiral_orbit_transitive`
- Truth anchor: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.chiral_vacuum_stabilizer_iff`
- Truth anchor: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.derrick_no_pure_sigma_soliton`
- Truth anchor: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.derrick_skyrme_virial_minimum`
- Truth anchor: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.faddeev_bogomolny_saturation_iff`
- Truth anchor: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.faddeev_bogomolny_skyrme_bound`
- Truth anchor: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.gmor_exact_hessian`
- Truth anchor: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.gmor_pion_mass_relation`
- Truth anchor: `D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D.su2SphereCoordinates`
