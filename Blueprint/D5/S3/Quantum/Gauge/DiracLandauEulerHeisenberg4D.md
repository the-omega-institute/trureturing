# Dirac magnetic levels and the Euler–Heisenberg action

## Abstract

The Dirac magnetic spin pairing and the weak-field electromagnetic effective action in four dimensions.

The transverse Pauli square fixes the coefficient of the magnetic spin shift. The quartic effective action then gives the polarization-dependent probe Hessians. In a purely electric field the vacuum-persistence series exhibits a separate exponential scale.

**Theorem 1.1 (Exact lowest-level cancellation).**

Lean statement: `D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.dirac_g2_zero_mode_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.dirac_g2_zero_mode_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Stephen L. Adler (1971). *Photon splitting and photon dispersion in a strong magnetic field*. DOI: [10.1016/0003-4916(71)90154-0](https://doi.org/10.1016/0003-4916(71)90154-0).

*Commentary.*

At positive magnetic coupling, the shift at oscillator label zero and spin label one half vanishes exactly when the gyromagnetic factor equals two. Equivalently the squared energy at that label equals the sum of squared mass and squared longitudinal momentum exactly at that factor.

**Theorem 1.2 (Multiplicity of the magnetic levels).**

Lean statement: `D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.dirac_landau_exact_twofold_degeneracy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.dirac_landau_exact_twofold_degeneracy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Stephen L. Adler (1971). *Photon splitting and photon dispersion in a strong magnetic field*. DOI: [10.1016/0003-4916(71)90154-0](https://doi.org/10.1016/0003-4916(71)90154-0).

*Commentary.*

For positive magnetic coupling and either permitted spin, attaining the level indexed by a natural number k is equivalent to having oscillator label k and spin one half, or having positive k, oscillator label k minus one, and spin minus one half. Thus level zero has exactly one label and every higher level has two.

**Theorem 1.3 (Pauli square in a linear magnetic gauge).**

Lean statement: `D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.dirac_pauli_square_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.dirac_pauli_square_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Stephen L. Adler (1971). *Photon splitting and photon dispersion in a strong magnetic field*. DOI: [10.1016/0003-4916(71)90154-0](https://doi.org/10.1016/0003-4916(71)90154-0).

*Commentary.*

The upper off-diagonal blocks of the three spatial Dirac matrices are the Pauli matrices. In a complex algebra where the free momenta commute and the first momentum has commutator minus the imaginary unit with position, adding the magnetic position term to the second momentum gives the transverse Pauli square with its unit Zeeman coefficient. The polynomial momentum operators also realize the identity for each Fourier momentum in the second coordinate.

**Theorem 1.4 (Hermite modes of the squared magnetic operator).**

Lean statement: `D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.dirac_landau_squared_energy_modes`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.dirac_landau_squared_energy_modes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Stephen L. Adler (1971). *Photon splitting and photon dispersion in a strong magnetic field*. DOI: [10.1016/0003-4916(71)90154-0](https://doi.org/10.1016/0003-4916(71)90154-0).

*Commentary.*

At positive magnetic coupling, every oscillator label and each Pauli spin component give a nonzero translated Hermite mode. The diagonal Pauli entry is minus twice the spin projection used in the energy formula. The squared magnetic operator applied to the mode is pointwise multiplication by the stated squared Landau energy.

**Theorem 1.5 (Lorentz invariance, reflections and null fields).**

Lean statement: `D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.euler_heisenberg_lorentz_and_cp_invariance`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.euler_heisenberg_lorentz_and_cp_invariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Stephen L. Adler (1971). *Photon splitting and photon dispersion in a strong magnetic field*. DOI: [10.1016/0003-4916(71)90154-0](https://doi.org/10.1016/0003-4916(71)90154-0).

*Commentary.*

The action is invariant under determinant-one metric-preserving Lorentz transformations and under the separate changes of sign of the electric and magnetic fields. It vanishes whenever both field invariants are zero.

**Theorem 1.6 (The quartic term under field rotation).**

Lean statement: `D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.euler_heisenberg_breaks_em_duality`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.euler_heisenberg_breaks_em_duality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Stephen L. Adler (1971). *Photon splitting and photon dispersion in a strong magnetic field*. DOI: [10.1016/0003-4916(71)90154-0](https://doi.org/10.1016/0003-4916(71)90154-0).

*Commentary.*

The covariant Maxwell stress tensor remains fixed. At twice the rotation angle the first invariant transforms as cosine times the first invariant minus twice sine times the second, and the second as cosine times the second plus half sine times the first. The quartic difference is three quarters of the difference between the first invariant squared and four times the second squared, times the squared sine, plus three times the product of the invariants times sine and cosine. A rotation changing the quartic exists exactly when at least one invariant is nonzero. At angle pi over four a pure magnetic field gives the quartic factor seven quarters and a zero linear Lagrangian.

**Theorem 1.7 (Probe Hessians and refractive index shifts).**

Lean statement: `D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.vacuum_birefringence_indices_and_subluminality`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.vacuum_birefringence_indices_and_subluminality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Stephen L. Adler (1971). *Photon splitting and photon dispersion in a strong magnetic field*. DOI: [10.1016/0003-4916(71)90154-0](https://doi.org/10.1016/0003-4916(71)90154-0).

*Commentary.*

For positive fine-structure constant, mass and background field with the stated charge relation, write u for the effective quartic coefficient times the squared field. The coefficients of the squared electric and magnetic amplitudes in the second derivative are one plus ten u and minus one plus four u for the parallel mode, and one minus four u and minus one plus twelve u for the perpendicular mode. The squared speeds are the negative magnetic-to-electric Hessian ratios. The two refractive indices have derivatives seven and four at u equal to zero. In critical-field units the first-order shifts are seven and four times alpha divided by ninety pi times the squared field ratio. Their ratio is seven quarters. Both squared speeds lie strictly between zero and one for u below one twelfth, where the parallel squared speed is smaller exactly when u is below three sixty-eighths.

**Theorem 1.8 (Quartic coefficient of the hyperbolic kernel).**

Lean statement: `D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.euler_heisenberg_coth_quartic_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.euler_heisenberg_coth_quartic_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Stephen L. Adler (1971). *Photon splitting and photon dispersion in a strong magnetic field*. DOI: [10.1016/0003-4916(71)90154-0](https://doi.org/10.1016/0003-4916(71)90154-0).

*Commentary.*

After subtracting one and the quadratic term from x times its hyperbolic cotangent, division by the fourth power has two-sided punctured limit minus one forty-fifth. In the combined fraction the denominator is the fourth power times the hyperbolic sine.

**Theorem 1.9 (Magnetic proper-time moment).**

Lean statement: `D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.euler_heisenberg_proper_time_quartic_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.euler_heisenberg_proper_time_quartic_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Stephen L. Adler (1971). *Photon splitting and photon dispersion in a strong magnetic field*. DOI: [10.1016/0003-4916(71)90154-0](https://doi.org/10.1016/0003-4916(71)90154-0).

*Commentary.*

For positive mass, the Lebesgue integral of proper time times the exponential of minus mass squared times proper time over the positive half-line is the inverse fourth power of the mass. Multiplying by the magnetic prefactor yields the pure magnetic quartic coefficient of the effective action, with fine-structure constant equal to squared charge divided by four pi.

**Theorem 1.10 (Electric series bounds and right-hand flatness).**

Lean statement: `D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.schwinger_pair_production_series_and_essential_singularity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.schwinger_pair_production_series_and_essential_singularity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Stephen L. Adler (1971). *Photon splitting and photon dispersion in a strong magnetic field*. DOI: [10.1016/0003-4916(71)90154-0](https://doi.org/10.1016/0003-4916(71)90154-0).

*Commentary.*

For positive charge, mass and electric field the Schwinger summands are summable. The rate lies between the first exponential term times its prefactor and the same exponential times squared charge-field product divided by twenty-four pi. For every natural power of the electric field, dividing the rate by that power yields limit zero at zero from the right.

## References

- Truth anchor: `D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.dirac_g2_zero_mode_iff`
- Truth anchor: `D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.dirac_landau_exact_twofold_degeneracy`
- Truth anchor: `D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.dirac_landau_squared_energy_modes`
- Truth anchor: `D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.dirac_pauli_square_identity`
- Truth anchor: `D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.euler_heisenberg_breaks_em_duality`
- Truth anchor: `D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.euler_heisenberg_coth_quartic_limit`
- Truth anchor: `D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.euler_heisenberg_lorentz_and_cp_invariance`
- Truth anchor: `D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.euler_heisenberg_proper_time_quartic_coeff`
- Truth anchor: `D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.schwinger_pair_production_series_and_essential_singularity`
- Truth anchor: `D5/S3/Quantum/Gauge/DiracLandauEulerHeisenberg4D.vacuum_birefringence_indices_and_subluminality`
- Dependency: [D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D](../../Geometry/Lorentz/DiracCliffordSpinors4D.md)
- Dependency: [D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D](../../Geometry/Lorentz/MaxwellRainichStressEnergy4D.md)
