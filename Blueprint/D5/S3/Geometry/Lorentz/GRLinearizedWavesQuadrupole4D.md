# Transverse-traceless waves and circular binary inspiral

## Abstract

Spin-two polarization and leading circular quadrupole radiation.

A unit propagation direction selects a two-dimensional spatial plane. On symmetric spatial strains, the transverse-traceless projection isolates two real polarization amplitudes, which rotate through twice the spatial angle. For a circular binary, the leading quadrupole flux and Newtonian binding energy give an explicit inspiral solution.

**Definition 1.1 (Unit propagation direction).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.IsUnitVec3`

*Formalization.* `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.IsUnitVec3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The three squared spatial components sum to one.

**Definition 1.2 (Transverse projection).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.transverseProj`

*Formalization.* `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.transverseProj` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtract the outer product of the direction vector from the identity.

**Definition 1.3 (Transverse-traceless projection).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.ttProj`

*Formalization.* `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.ttProj` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Project on both matrix indices, then subtract half the projected trace times the transverse projector.

**Theorem 1.4 (Transverse projection properties).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.transverseProj_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.transverseProj_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a unit direction the projector is symmetric and idempotent, sends the direction to zero, and has trace two.

**Theorem 1.5 (Symmetry of projected strains).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.ttProj_symmetric`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.ttProj_symmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A symmetric input gives a symmetric output.

**Theorem 1.6 (Transversality of the projection).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.ttProj_transverse`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.ttProj_transverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a unit direction, the projected matrix sends the direction to zero.

**Theorem 1.7 (Trace of the projection).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.ttProj_traceless`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.ttProj_traceless` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a unit direction, the transverse subtraction cancels the projected trace.

**Theorem 1.8 (Idempotence of the projection).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.ttProj_idempotent`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.ttProj_idempotent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a unit direction, the output of the first projection is fixed by a second projection.

**Theorem 1.9 (Self-adjointness of the projection).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.ttProj_selfAdjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.ttProj_selfAdjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transposing products and cycling the trace show self-adjointness for the real matrix inner product.

**Definition 1.10 (Plus polarization).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.ePlus`

*Formalization.* `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.ePlus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first two diagonal entries are one and minus one, with all other entries zero.

**Definition 1.11 (Cross polarization).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.eCross`

*Formalization.* `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.eCross` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first two off-diagonal entries are one, with all other entries zero.

**Definition 1.12 (Strain amplitudes).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.gwStrainZ`

*Formalization.* `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.gwStrainZ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply the plus and cross matrices by their respective real amplitudes and add them.

**Theorem 1.13 (Classification along the z axis).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.tt_z_classification`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.tt_z_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

A symmetric matrix transverse to the z axis and of trace zero is exactly a plus and cross strain.

**Theorem 1.14 (Unique polarization coordinates).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.tt_z_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.tt_z_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first diagonal entry and first off-diagonal entry recover the plus and cross amplitudes.

**Definition 1.15 (Transverse-traceless subspace).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.TTSubspaceZ`

*Formalization.* `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.TTSubspaceZ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The subspace consists of symmetric traceless matrices whose product with the z unit vector is zero.

**Theorem 1.16 (Polarization dimension).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.tt_z_finrank_two`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.tt_z_finrank_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The polarization coordinates give a linear equivalence with pairs of reals, so the subspace has dimension two.

**Definition 1.17 (Rotation around the propagation axis).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.rotZ3`

*Formalization.* `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.rotZ3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply the usual real rotation in the first two spatial coordinates and fix the third coordinate.

**Theorem 1.18 (Spin-two rotation law).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.gw_strain_helicity_two`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.gw_strain_helicity_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

Conjugation by the spatial rotation sends the polarization pair to its rotation through twice the spatial angle. The complex combinations therefore carry helicities plus and minus two.

**Theorem 1.19 (Half-turn invariance).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.gw_strain_pi_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.gw_strain_pi_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A spatial rotation through pi leaves the strain fixed.

**Theorem 1.20 (Quarter-turn sign).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.gw_strain_half_pi_neg`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.gw_strain_half_pi_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A spatial rotation through pi over two negates the strain.

**Theorem 1.21 (Squared strain norm).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.gw_strain_hilbert_schmidt_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.gw_strain_hilbert_schmidt_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace of the squared strain is twice the sum of the squared polarization amplitudes.

**Definition 1.22 (Circular mass quadrupole).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.binaryQuadrupole`

*Formalization.* `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.binaryQuadrupole` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Remove one third the squared radius times the identity from the outer product of the circular orbit position and multiply by the reduced mass.

**Definition 1.23 (First quadrupole derivative).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.binaryQuadrupoleD1`

*Formalization.* `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.binaryQuadrupoleD1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The varying entries are in the orbital plane and use the sine and cosine of twice the orbital angle.

**Definition 1.24 (Second quadrupole derivative).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.binaryQuadrupoleD2`

*Formalization.* `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.binaryQuadrupoleD2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The second derivative is supported in the orbital plane, with its harmonic entries proportional to the square of the angular velocity.

**Definition 1.25 (Third quadrupole derivative).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.binaryQuadrupoleD3`

*Formalization.* `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.binaryQuadrupoleD3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The planar diagonal entries are opposite sine harmonics and the off-diagonal entries are negative cosine harmonics, with common factor four times the reduced mass, squared radius and cubed angular velocity.

**Theorem 1.26 (Symmetric quadrupole).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.binaryQuadrupole_symmetric`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.binaryQuadrupole_symmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The outer product and trace subtraction are symmetric.

**Theorem 1.27 (Zero quadrupole trace).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.binaryQuadrupole_traceless`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.binaryQuadrupole_traceless` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The circular sine and cosine squares sum to one, so the orbital trace equals the subtracted trace.

**Theorem 1.28 (First entrywise derivative).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.binaryQuadrupole_hasDerivAt_1`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.binaryQuadrupole_hasDerivAt_1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each entry of the quadrupole differentiates to the matching entry of the first derivative matrix.

**Theorem 1.29 (Second entrywise derivative).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.binaryQuadrupole_hasDerivAt_2`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.binaryQuadrupole_hasDerivAt_2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each entry of the first derivative differentiates to the matching entry of the second derivative matrix.

**Theorem 1.30 (Third entrywise derivative).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.binaryQuadrupole_hasDerivAt_3`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.binaryQuadrupole_hasDerivAt_3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each entry of the second derivative differentiates to the matching entry of the third derivative matrix.

**Theorem 1.31 (Time-independent derivative norm).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.binaryQuadrupole_third_deriv_norm_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.binaryQuadrupole_third_deriv_norm_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. C. Peters and J. Mathews (1963). *Gravitational Radiation from Point Masses in a Keplerian Orbit*. DOI: [10.1103/PhysRev.131.435](https://doi.org/10.1103/PhysRev.131.435). URL: <https://journals.aps.org/pr/abstract/10.1103/PhysRev.131.435>.

*Commentary.*

The squared sine and cosine contributions sum to thirty-two times the squared reduced mass, fourth power of the radius and sixth power of the angular velocity.

**Definition 1.32 (Chirp mass).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.chirpMass`

*Formalization.* `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.chirpMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Raise the component-mass product to three fifths and divide by the total mass to one fifth.

**Definition 1.33 (Quadrupole power).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.quadrupolePower`

*Formalization.* `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.quadrupolePower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply the third derivative norm squared by the gravitational constant divided by five times the fifth power of light speed.

**Definition 1.34 (Circular binary power).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.pmPower`

*Formalization.* `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.pmPower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The power for positive component masses and radius varies inversely as the fifth power of separation.

**Theorem 1.35 (Peters-Mathews circular power).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.peters_mathews_circular_power`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.peters_mathews_circular_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. C. Peters and J. Mathews (1963). *Gravitational Radiation from Point Masses in a Keplerian Orbit*. DOI: [10.1103/PhysRev.131.435](https://doi.org/10.1103/PhysRev.131.435). URL: <https://journals.aps.org/pr/abstract/10.1103/PhysRev.131.435>.

*Commentary.*

With Kepler's law, the circular quadrupole power equals the separation formula with the fourth power of the gravitational constant and inverse fifth power of light speed.

**Theorem 1.36 (Power expressed with chirp mass).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.peters_mathews_chirp_power`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.peters_mathews_chirp_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. C. Peters and J. Mathews (1963). *Gravitational Radiation from Point Masses in a Keplerian Orbit*. DOI: [10.1103/PhysRev.131.435](https://doi.org/10.1103/PhysRev.131.435). URL: <https://journals.aps.org/pr/abstract/10.1103/PhysRev.131.435>.

*Commentary.*

For the positive Kepler frequency the circular power is proportional to the ten-thirds power of gravitational constant times chirp mass times angular velocity divided by light speed cubed.

**Theorem 1.37 (Equal-mass maximum).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.chirpMass_le_equal_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.chirpMass_le_equal_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For fixed positive total mass, the chirp mass is at most the total mass times two to the power minus six fifths. Equality holds exactly for equal component masses.

**Definition 1.38 (Newtonian orbital energy).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.orbitalEnergy`

*Formalization.* `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.orbitalEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The binding energy is minus the gravitational constant times the mass product divided by twice the radius.

**Definition 1.39 (Coalescence time).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.coalescenceTime`

*Formalization.* `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.coalescenceTime` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coalescence time is proportional to the fourth power of the initial radius with the coefficient fixed by energy balance.

**Definition 1.40 (Circular inspiral radius).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.inspiralRadius`

*Formalization.* `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.inspiralRadius` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Scale the initial radius by the fourth root of one minus the elapsed fraction of coalescence time.

**Theorem 1.41 (Inspiral radius derivative).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.inspiralRadius_hasDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.inspiralRadius_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Before coalescence the derivative is negative and proportional to the inverse cube of the instantaneous radius.

**Theorem 1.42 (Radiative energy balance).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.inspiral_satisfies_energy_balance`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.inspiral_satisfies_energy_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. C. Peters and J. Mathews (1963). *Gravitational Radiation from Point Masses in a Keplerian Orbit*. DOI: [10.1103/PhysRev.131.435](https://doi.org/10.1103/PhysRev.131.435). URL: <https://journals.aps.org/pr/abstract/10.1103/PhysRev.131.435>.

*Commentary.*

The derivative of the Newtonian orbital energy along the inspiral is minus the circular radiated power.

**Theorem 1.43 (Initial and coalescence radii).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.inspiral_coalescence_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.inspiral_coalescence_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The radius is its prescribed initial value at time zero and tends to zero from below in time at coalescence.

**Definition 1.44 (Gravitational-wave frequency).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.gwFreq`

*Formalization.* `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.gwFreq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Divide the positive Kepler angular velocity by pi to get twice the orbital cyclic frequency.

**Theorem 1.45 (Chirp frequency equation).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.gw_chirp_frequency_ode`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.gw_chirp_frequency_ode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. C. Peters and J. Mathews (1963). *Gravitational Radiation from Point Masses in a Keplerian Orbit*. DOI: [10.1103/PhysRev.131.435](https://doi.org/10.1103/PhysRev.131.435). URL: <https://journals.aps.org/pr/abstract/10.1103/PhysRev.131.435>.

*Commentary.*

Before coalescence the frequency derivative is ninety-six fifths times pi to eight thirds, the scaled chirp mass to five thirds, and the instantaneous frequency to eleven thirds.

**Theorem 1.46 (Linear inverse frequency power).**

Lean statement: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.gw_chirp_frequency_inv_power_linear`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.gw_chirp_frequency_inv_power_linear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Before coalescence, the frequency raised to minus eight thirds equals its initial value to the same power multiplied by one minus the elapsed fraction of coalescence time.

## References

- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.IsUnitVec3`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.TTSubspaceZ`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.binaryQuadrupole`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.binaryQuadrupoleD1`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.binaryQuadrupoleD2`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.binaryQuadrupoleD3`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.binaryQuadrupole_hasDerivAt_1`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.binaryQuadrupole_hasDerivAt_2`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.binaryQuadrupole_hasDerivAt_3`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.binaryQuadrupole_symmetric`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.binaryQuadrupole_third_deriv_norm_sq`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.binaryQuadrupole_traceless`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.chirpMass`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.chirpMass_le_equal_mass`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.coalescenceTime`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.eCross`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.ePlus`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.gwFreq`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.gwStrainZ`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.gw_chirp_frequency_inv_power_linear`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.gw_chirp_frequency_ode`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.gw_strain_half_pi_neg`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.gw_strain_helicity_two`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.gw_strain_hilbert_schmidt_energy`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.gw_strain_pi_invariant`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.inspiralRadius`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.inspiralRadius_hasDerivAt`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.inspiral_coalescence_limit`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.inspiral_satisfies_energy_balance`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.orbitalEnergy`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.peters_mathews_chirp_power`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.peters_mathews_circular_power`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.pmPower`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.quadrupolePower`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.rotZ3`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.transverseProj`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.transverseProj_spec`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.ttProj`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.ttProj_idempotent`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.ttProj_selfAdjoint`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.ttProj_symmetric`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.ttProj_traceless`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.ttProj_transverse`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.tt_z_classification`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.tt_z_coordinates`
- Truth anchor: `D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D.tt_z_finrank_two`
