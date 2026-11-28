# Kerr ergosphere and equatorial orbits

## Abstract

Stationary limits, horizon rotation, extraction, and equatorial Kerr orbits.

The Kerr horizon is a root of the radial polynomial. The outer stationary limit instead comes from the time component of the metric. Between these two surfaces every stationary timelike observer rotates with the black hole.

**Definition 1.1 (Radial polynomial).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.kerrDelta`

*Formalization.* `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.kerrDelta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* James M. Bardeen, William H. Press, and Saul A. Teukolsky (1972). *Rotating Black Holes: Locally Nonrotating Frames, Energy Extraction, and Scalar Synchrotron Radiation*. DOI: [10.1086/151796](https://doi.org/10.1086/151796). URL: <https://doi.org/10.1086/151796>.

*Commentary.*

Add the squared radius and squared spin and subtract twice the mass times the radius.

**Definition 1.2 (Latitude factor).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.kerrSigma`

*Formalization.* `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.kerrSigma` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* James M. Bardeen, William H. Press, and Saul A. Teukolsky (1972). *Rotating Black Holes: Locally Nonrotating Frames, Energy Extraction, and Scalar Synchrotron Radiation*. DOI: [10.1086/151796](https://doi.org/10.1086/151796). URL: <https://doi.org/10.1086/151796>.

*Commentary.*

Add the squared radius and squared spin times squared cosine of the polar angle.

**Definition 1.3 (Azimuthal metric factor).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.kerrA`

*Formalization.* `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.kerrA` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* James M. Bardeen, William H. Press, and Saul A. Teukolsky (1972). *Rotating Black Holes: Locally Nonrotating Frames, Energy Extraction, and Scalar Synchrotron Radiation*. DOI: [10.1086/151796](https://doi.org/10.1086/151796). URL: <https://doi.org/10.1086/151796>.

*Commentary.*

Subtract the radial polynomial times squared spin and squared sine from the square of the sum of squared radius and squared spin.

**Theorem 1.4 (Time and azimuth determinant).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.kerr_metric_2d_det`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.kerr_metric_2d_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* James M. Bardeen, William H. Press, and Saul A. Teukolsky (1972). *Rotating Black Holes: Locally Nonrotating Frames, Energy Extraction, and Scalar Synchrotron Radiation*. DOI: [10.1086/151796](https://doi.org/10.1086/151796). URL: <https://doi.org/10.1086/151796>.

*Commentary.*

When the latitude factor is nonzero, the determinant equals minus the radial polynomial times squared sine.

**Theorem 1.5 (Horizon factorization).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.kerrDelta_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.kerrDelta_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* James M. Bardeen, William H. Press, and Saul A. Teukolsky (1972). *Rotating Black Holes: Locally Nonrotating Frames, Energy Extraction, and Scalar Synchrotron Radiation*. DOI: [10.1086/151796](https://doi.org/10.1086/151796). URL: <https://doi.org/10.1086/151796>.

*Commentary.*

The radial polynomial factors into the differences from the outer and inner horizon radii when the absolute spin is at most the mass.

**Theorem 1.6 (Separation from the horizon).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.ergosphere_strictly_outside_horizon`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.ergosphere_strictly_outside_horizon` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* James M. Bardeen, William H. Press, and Saul A. Teukolsky (1972). *Rotating Black Holes: Locally Nonrotating Frames, Energy Extraction, and Scalar Synchrotron Radiation*. DOI: [10.1086/151796](https://doi.org/10.1086/151796). URL: <https://doi.org/10.1086/151796>.

*Commentary.*

The stationary limit lies at or above the outer horizon. For nonzero spin the separation is strict exactly where the sine of the polar angle is nonzero.

**Theorem 1.7 (Spacelike time translation).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.g_tt_positive_in_ergosphere`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.g_tt_positive_in_ergosphere` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* James M. Bardeen, William H. Press, and Saul A. Teukolsky (1972). *Rotating Black Holes: Locally Nonrotating Frames, Energy Extraction, and Scalar Synchrotron Radiation*. DOI: [10.1086/151796](https://doi.org/10.1086/151796). URL: <https://doi.org/10.1086/151796>.

*Commentary.*

For positive mass between the outer horizon and stationary limit, the norm squared of the time-translation Killing vector is positive.

**Theorem 1.8 (Horizon angular velocity).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.frameDrag_at_horizon_rigid`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.frameDrag_at_horizon_rigid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* James M. Bardeen, William H. Press, and Saul A. Teukolsky (1972). *Rotating Black Holes: Locally Nonrotating Frames, Energy Extraction, and Scalar Synchrotron Radiation*. DOI: [10.1086/151796](https://doi.org/10.1086/151796). URL: <https://doi.org/10.1086/151796>.

*Commentary.*

Away from the axis the frame angular velocity at the outer horizon equals the spin divided by twice the product of mass and horizon radius.

**Theorem 1.9 (Open timelike angular interval).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.timelike_omega_window_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.timelike_omega_window_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* James M. Bardeen, William H. Press, and Saul A. Teukolsky (1972). *Rotating Black Holes: Locally Nonrotating Frames, Energy Extraction, and Scalar Synchrotron Radiation*. DOI: [10.1086/151796](https://doi.org/10.1086/151796). URL: <https://doi.org/10.1086/151796>.

*Commentary.*

Outside the horizon and away from the axis the circular norm factors into the azimuthal coefficient and the two differences from the null angular velocities. The norm is negative exactly between those velocities.

**Theorem 1.10 (Exterior metric signature).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.kerr_exterior_metric_signature`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.kerr_exterior_metric_signature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* James M. Bardeen, William H. Press, and Saul A. Teukolsky (1972). *Rotating Black Holes: Locally Nonrotating Frames, Energy Extraction, and Scalar Synchrotron Radiation*. DOI: [10.1086/151796](https://doi.org/10.1086/151796). URL: <https://doi.org/10.1086/151796>.

*Commentary.*

Completing the time and azimuth square gives one negative and three positive diagonal coefficients outside the outer horizon and away from the axis.

**Theorem 1.11 (Mandatory co-rotation).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.ergosphere_forbids_static_observer`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.ergosphere_forbids_static_observer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* James M. Bardeen, William H. Press, and Saul A. Teukolsky (1972). *Rotating Black Holes: Locally Nonrotating Frames, Energy Extraction, and Scalar Synchrotron Radiation*. DOI: [10.1086/151796](https://doi.org/10.1086/151796). URL: <https://doi.org/10.1086/151796>.

*Commentary.*

For positive spin in the ergoregion, the lower null angular velocity is positive, the static circular vector is spacelike, and every timelike circular vector has positive angular velocity.

**Theorem 1.12 (Penrose energy gain).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.penrose_extraction_forces_retrograde`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.penrose_extraction_forces_retrograde` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* James M. Bardeen, William H. Press, and Saul A. Teukolsky (1972). *Rotating Black Holes: Locally Nonrotating Frames, Energy Extraction, and Scalar Synchrotron Radiation*. DOI: [10.1086/151796](https://doi.org/10.1086/151796). URL: <https://doi.org/10.1086/151796>.

*Commentary.*

The future horizon inequality forces the captured particle's angular momentum to be negative when its Killing energy is negative. Energy conservation in the split then bounds the escaping energy strictly above the incoming energy.

**Theorem 1.13 (Area and irreducible mass).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.penrose_area_nondecrease_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.penrose_area_nondecrease_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* James M. Bardeen, William H. Press, and Saul A. Teukolsky (1972). *Rotating Black Holes: Locally Nonrotating Frames, Energy Extraction, and Scalar Synchrotron Radiation*. DOI: [10.1086/151796](https://doi.org/10.1086/151796). URL: <https://doi.org/10.1086/151796>.

*Commentary.*

For neutral subextremal Kerr along differentiable thermodynamic curves, the area derivative, the irreducible-mass derivative, and the mass derivative minus horizon angular velocity times angular momentum derivative have the same nonnegative sign.

**Theorem 1.14 (Superradiance threshold).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.superradiance_condition_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.superradiance_condition_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* James M. Bardeen, William H. Press, and Saul A. Teukolsky (1972). *Rotating Black Holes: Locally Nonrotating Frames, Energy Extraction, and Scalar Synchrotron Radiation*. DOI: [10.1086/151796](https://doi.org/10.1086/151796). URL: <https://doi.org/10.1086/151796>.

*Commentary.*

With positive frequency and flux coefficient the horizon energy flux is negative exactly when the frequency is less than the azimuthal number times the angular velocity of the horizon.

**Theorem 1.15 (Photon radii).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.kerr_photon_orbit_benchmarks`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.kerr_photon_orbit_benchmarks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* James M. Bardeen, William H. Press, and Saul A. Teukolsky (1972). *Rotating Black Holes: Locally Nonrotating Frames, Energy Extraction, and Scalar Synchrotron Radiation*. DOI: [10.1086/151796](https://doi.org/10.1086/151796). URL: <https://doi.org/10.1086/151796>.

*Commentary.*

For positive radius the nonrotating polynomial vanishes at the stationary radius of the Schwarzschild null potential. At extremal spin the polynomial has a double root at one mass and a simple root at four masses.

**Theorem 1.16 (Extremal photon directions).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.extremal_photon_orbit_directions`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.extremal_photon_orbit_directions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* James M. Bardeen, William H. Press, and Saul A. Teukolsky (1972). *Rotating Black Holes: Locally Nonrotating Frames, Energy Extraction, and Scalar Synchrotron Radiation*. DOI: [10.1086/151796](https://doi.org/10.1086/151796). URL: <https://doi.org/10.1086/151796>.

*Commentary.*

The signed circular-photon equation assigns one mass to the prograde root and four masses to the retrograde root.

**Theorem 1.17 (Unique positive extremal marginal radii).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.extremal_isco_radii_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.extremal_isco_radii_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* James M. Bardeen, William H. Press, and Saul A. Teukolsky (1972). *Rotating Black Holes: Locally Nonrotating Frames, Energy Extraction, and Scalar Synchrotron Radiation*. DOI: [10.1086/151796](https://doi.org/10.1086/151796). URL: <https://doi.org/10.1086/151796>.

*Commentary.*

The signed marginal-stability equations factor in the dimensionless square-root radius, leaving one positive root for each direction.

**Theorem 1.18 (Marginal stability and binding efficiency).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.kerr_isco_benchmarks_and_binding_efficiency`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.kerr_isco_benchmarks_and_binding_efficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* James M. Bardeen, William H. Press, and Saul A. Teukolsky (1972). *Rotating Black Holes: Locally Nonrotating Frames, Energy Extraction, and Scalar Synchrotron Radiation*. DOI: [10.1086/151796](https://doi.org/10.1086/151796). URL: <https://doi.org/10.1086/151796>.

*Commentary.*

The nonrotating radius is six masses. The extremal prograde and retrograde radii are one and nine masses. The positive binding efficiencies increase in the order retrograde, Schwarzschild, prograde, and all are below one half.

**Theorem 1.19 (Energy at marginal stability).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.isco_efficiency_eq_orbit_binding`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.isco_efficiency_eq_orbit_binding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* James M. Bardeen, William H. Press, and Saul A. Teukolsky (1972). *Rotating Black Holes: Locally Nonrotating Frames, Energy Extraction, and Scalar Synchrotron Radiation*. DOI: [10.1086/151796](https://doi.org/10.1086/151796). URL: <https://doi.org/10.1086/151796>.

*Commentary.*

At a positive marginally stable radius, on the timelike branch with nonnegative specific energy, the circular-orbit energy is the square root of one minus two masses divided by three radii.

**Theorem 1.20 (Extremal prograde energy limit).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.extremal_prograde_energy_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.extremal_prograde_energy_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* James M. Bardeen, William H. Press, and Saul A. Teukolsky (1972). *Rotating Black Holes: Locally Nonrotating Frames, Energy Extraction, and Scalar Synchrotron Radiation*. DOI: [10.1086/151796](https://doi.org/10.1086/151796). URL: <https://doi.org/10.1086/151796>.

*Commentary.*

Factoring the numerator and the square-root argument cancels a common factor on the exterior. As the dimensionless square-root radius tends to one from above, the specific energy tends to the reciprocal of square root of three.

## References

- Truth anchor: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.ergosphere_forbids_static_observer`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.ergosphere_strictly_outside_horizon`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.extremal_isco_radii_unique`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.extremal_photon_orbit_directions`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.extremal_prograde_energy_limit`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.frameDrag_at_horizon_rigid`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.g_tt_positive_in_ergosphere`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.isco_efficiency_eq_orbit_binding`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.kerrA`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.kerrDelta`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.kerrDelta_factorization`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.kerrSigma`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.kerr_exterior_metric_signature`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.kerr_isco_benchmarks_and_binding_efficiency`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.kerr_metric_2d_det`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.kerr_photon_orbit_benchmarks`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.penrose_area_nondecrease_iff`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.penrose_extraction_forces_retrograde`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.superradiance_condition_iff`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D.timelike_omega_window_iff`
- Dependency: [D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D](BlackHoleThermodynamics4D.md)
- Dependency: [D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D](SchwarzschildOpticalGeodesics4D.md)
