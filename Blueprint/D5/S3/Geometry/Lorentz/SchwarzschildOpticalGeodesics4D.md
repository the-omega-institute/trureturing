# Schwarzschild optical and timelike orbits

## Abstract

Schwarzschild effective potentials yield the photon sphere, critical impact parameter, marginally stable circular orbit and first-order deflection.

In geometric units, the null potential has its unique positive-radius maximum at three times the mass. The circular timelike family changes stability at six times the mass. Static clock ratios use the Schwarzschild lapse, and the angular endpoint calculation gives the first-order bending angle for weak fields.

**Definition 1.1 (Null effective potential).**

Lean statement: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.nullPotential`

*Formalization.* `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.nullPotential` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

Divide the Schwarzschild lapse squared by the areal radius squared.

**Theorem 1.2 (Radial derivative).**

Lean statement: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.nullPotential_hasDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.nullPotential_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At any nonzero radius the derivative is twice the difference between three masses and the radius, divided by the radius to the fourth power.

**Theorem 1.3 (Unique positive stationary radius).**

Lean statement: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.photon_sphere_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.photon_sphere_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The null potential derivative at a positive radius vanishes exactly at three times the mass.

**Theorem 1.4 (Global maximum of the null potential).**

Lean statement: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.photon_sphere_strict_global_max`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.photon_sphere_strict_global_max` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive mass and radius the potential is at most 1/(27 M²), with equality exactly at r = 3M. The gap factors as a positive factor times (r − 3M)².

**Theorem 1.5 (Negative radial curvature).**

Lean statement: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.photon_sphere_unstable`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.photon_sphere_unstable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At three times the mass the second derivative is minus two divided by eighty-one times the fourth power of the mass.

**Theorem 1.6 (Critical impact parameter).**

Lean statement: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.shadow_critical_impact_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.shadow_critical_impact_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse maximum is twenty-seven times the squared mass. Its square root is three times the square root of three times the mass.

**Theorem 1.7 (Null capture threshold).**

Lean statement: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.shadow_capture_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.shadow_capture_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive impact parameter the inverse squared impact parameter exceeds the potential maximum exactly below the critical impact parameter.

**Definition 1.8 (Timelike effective potential).**

Lean statement: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.timePotential`

*Formalization.* `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.timePotential` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

Multiply one half of the lapse squared by one plus the squared angular momentum divided by the squared radius.

**Theorem 1.9 (Timelike radial derivative).**

Lean statement: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.timePotential_hasDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.timePotential_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At any nonzero radius the derivative numerator is the mass times the squared radius minus the squared angular momentum times the difference between radius and three masses. The denominator is the fourth power of the radius.

**Theorem 1.10 (Circular angular momentum).**

Lean statement: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.circular_orbit_angMom_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.circular_orbit_angMom_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive mass and r > 3M, the potential derivative vanishes exactly when L² = M r²/(r − 3M).

**Theorem 1.11 (Inner exclusion).**

Lean statement: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.no_circular_orbit_le_threeM`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.no_circular_orbit_le_threeM` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive mass there is no stationary timelike potential at a positive radius at or below three times the mass.

**Theorem 1.12 (Circular radial curvature).**

Lean statement: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.circular_orbit_second_deriv`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.circular_orbit_second_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At fixed circular-orbit angular momentum, the second derivative is the mass times the difference from six masses divided by the cubed radius and the difference from three masses.

**Theorem 1.13 (Stability and marginal radius).**

Lean statement: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.circular_orbit_stability_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.circular_orbit_stability_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second derivative is positive above six masses, zero there and negative below it on the circular timelike family.

**Theorem 1.14 (Parameters at the marginal orbit).**

Lean statement: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.isco_parameters_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.isco_parameters_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The squared angular momentum is twelve times the squared mass and the squared energy is eight ninths. The binding efficiency is one minus two times the square root of two divided by three.

**Theorem 1.15 (Minimum circular energy).**

Lean statement: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.circular_orbit_energy_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.circular_orbit_energy_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The squared specific energy is minimized exactly at six times the mass. The energy deficit from a particle at rest at infinity is maximal there.

**Definition 1.16 (Static clock ratio).**

Lean statement: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.redshiftRatio`

*Formalization.* `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.redshiftRatio` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

Divide the two squared lapses and take the nonnegative square root.

**Theorem 1.17 (Ordered clock rates).**

Lean statement: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.schwarzschild_redshift_factor`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.schwarzschild_redshift_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

For positive mass the clock at the smaller exterior radius has a positive rate strictly below that of the outer clock.

**Theorem 1.18 (Horizon limit).**

Lean statement: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.schwarzschild_redshift_horizon_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.schwarzschild_redshift_horizon_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

As the inner radius tends to the horizon from above the rate ratio to a fixed exterior clock tends to zero.

**Definition 1.19 (Unperturbed inverse radius).**

Lean statement: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.u0`

*Formalization.* `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.u0` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

The leading inverse-radius profile is the sine of the polar angle divided by the impact parameter.

**Definition 1.20 (First-order inverse-radius correction).**

Lean statement: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.u1`

*Formalization.* `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.u1` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

The correction is the mass divided by squared impact parameter times one plus the squared cosine of the polar angle.

**Theorem 1.21 (Zeroth-order Binet equation).**

Lean statement: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.binet_zeroth_order_ode`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.binet_zeroth_order_ode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second angular derivative plus the profile vanishes at every angle.

**Theorem 1.22 (First-order Binet equation).**

Lean statement: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.binet_first_order_ode`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.binet_first_order_ode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second angular derivative of the correction plus the correction equals three times the mass times the squared zeroth-order profile.

**Theorem 1.23 (First-order light deflection).**

Lean statement: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.einstein_light_deflection_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.einstein_light_deflection_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The difference of the linearized endpoint shifts at zero and pi is four times the mass divided by impact parameter.

## References

- Truth anchor: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.binet_first_order_ode`
- Truth anchor: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.binet_zeroth_order_ode`
- Truth anchor: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.circular_orbit_angMom_iff`
- Truth anchor: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.circular_orbit_energy_minimum`
- Truth anchor: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.circular_orbit_second_deriv`
- Truth anchor: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.circular_orbit_stability_iff`
- Truth anchor: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.einstein_light_deflection_eq`
- Truth anchor: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.isco_parameters_exact`
- Truth anchor: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.no_circular_orbit_le_threeM`
- Truth anchor: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.nullPotential`
- Truth anchor: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.nullPotential_hasDerivAt`
- Truth anchor: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.photon_sphere_strict_global_max`
- Truth anchor: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.photon_sphere_unique`
- Truth anchor: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.photon_sphere_unstable`
- Truth anchor: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.redshiftRatio`
- Truth anchor: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.schwarzschild_redshift_factor`
- Truth anchor: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.schwarzschild_redshift_horizon_limit`
- Truth anchor: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.shadow_capture_iff`
- Truth anchor: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.shadow_critical_impact_eq`
- Truth anchor: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.timePotential`
- Truth anchor: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.timePotential_hasDerivAt`
- Truth anchor: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.u0`
- Truth anchor: `D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D.u1`
