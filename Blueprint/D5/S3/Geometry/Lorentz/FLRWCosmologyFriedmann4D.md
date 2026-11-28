# Four-dimensional FLRW cosmology

## Abstract

Friedmann conservation, exact fluid and dust-vacuum expansion, and conformal horizons.

The Friedmann equations use cosmological time and a positive scale factor. Newton's constant is explicit and the cosmological constant is separate from the fluid density.

**Theorem 1.1 (Energy conservation).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.friedmann_implies_continuity`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.friedmann_implies_continuity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

The first Friedmann equation holds near the time in question and the acceleration equation holds at that time. Differentiating the curvature-inclusive first equation and using the acceleration equation leaves the continuity expression multiplied by minus eight pi G times the square of the scale factor divided by three. Positive Newton's constant and scale factor permit cancellation.

**Theorem 1.2 (Conserved first integral).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.continuity_and_friedmann_II_conserve_first_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.continuity_and_friedmann_II_conserve_first_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

The continuity and acceleration equations make the derivative of the squared velocity minus the density and cosmological terms zero.

**Definition 1.3 (Constant pressure ratio density).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.eosDensity`

*Formalization.* `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.eosDensity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

Multiply the reference density by the scale-factor ratio raised to minus three times one plus the pressure ratio.

**Theorem 1.4 (Continuity for a constant pressure ratio).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.eosDensity_continuity_ode`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.eosDensity_continuity_ode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

At positive reference and current scale factors, the density derivative is minus three times the product of the Hubble rate, one plus the pressure ratio, and the density.

**Theorem 1.5 (Dust, radiation and vacuum).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.eosDensity_dust_radiation_vacuum`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.eosDensity_dust_radiation_vacuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

For a nonnegative scale-factor ratio, the dust and radiation densities divide the reference density by the third and fourth powers of the ratio. The vacuum density is constant.

**Theorem 1.6 (Fluid acceleration threshold).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.acceleration_iff_strong_energy_violation`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.acceleration_iff_strong_energy_violation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

At zero cosmological constant and positive scale factor, Newton's constant and density, the acceleration is positive exactly when the pressure ratio is below minus one third.

**Theorem 1.7 (Dust acceleration threshold).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.dust_acceleration_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.dust_acceleration_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

At positive scale factor in the dust acceleration equation, the acceleration is positive exactly when the cosmological constant exceeds four pi G times the dust density.

**Definition 1.8 (Flat fluid exponent).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.flatExponent`

*Formalization.* `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.flatExponent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

Divide two by three times one plus the pressure ratio.

**Definition 1.9 (Power-law scale factor).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.flatScaleFactor`

*Formalization.* `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.flatScaleFactor` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

Multiply the indicated power of cosmological time by the normalization.

**Definition 1.10 (Power-law density).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.flatDensity`

*Formalization.* `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.flatDensity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

Take the reciprocal of six pi G times the square of one plus the pressure ratio times squared time.

**Definition 1.11 (Hubble rate).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.hubble`

*Formalization.* `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.hubble` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

Divide the time derivative of the scale factor by the scale factor.

**Definition 1.12 (Deceleration parameter).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.deceleration`

*Formalization.* `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.deceleration` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

Divide minus the product of the scale factor and its second derivative by the squared first derivative.

**Theorem 1.13 (Exact flat fluid solution).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.flat_power_law_satisfies_friedmann`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.flat_power_law_satisfies_friedmann` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

For positive time, normalization and Newton's constant and pressure ratio above minus one, the squared Hubble rate is eight pi G times the explicit density divided by three. The normalized second derivative is minus four pi G times the density and one plus three times the pressure ratio, divided by three.

**Theorem 1.14 (Age and Hubble rate).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.flat_power_law_hubble_age`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.flat_power_law_hubble_age` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

For positive time and scale normalization, the product of the Hubble rate and time is the power-law exponent.

**Theorem 1.15 (Age for dust and radiation).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.flat_dust_radiation_age`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.flat_dust_radiation_age` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

For positive time and scale normalization, the age is two divided by three times the Hubble rate for dust and one divided by twice that rate for radiation.

**Theorem 1.16 (Exact constant deceleration parameter).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.flat_power_law_deceleration`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.flat_power_law_deceleration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

For pressure ratio above minus one and positive time and normalization, the deceleration parameter is half of one plus three times the pressure ratio.

**Theorem 1.17 (Deceleration thresholds).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.flat_deceleration_thresholds`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.flat_deceleration_thresholds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

The deceleration parameter is one half for dust and one for radiation. For pressure ratio above minus one, it is negative exactly below minus one third.

**Definition 1.18 (Dust and vacuum scale factor).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdmScaleFactor`

*Formalization.* `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdmScaleFactor` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

Multiply the scale normalization by the two-thirds power of the hyperbolic sine of three halves times the vacuum Hubble rate times time.

**Definition 1.19 (Dust density).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdmDensity`

*Formalization.* `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdmDensity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

Divide the squared vacuum Hubble rate times the cubed ratio of normalization to scale factor by eight pi G divided by three.

**Theorem 1.20 (Dust and vacuum Hubble rate).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdm_hubble_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdm_hubble_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

For positive normalization, vacuum Hubble rate and time, the Hubble rate is the vacuum Hubble rate times the hyperbolic cotangent of the scale-factor argument.

**Theorem 1.21 (First flat dust and vacuum equation).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdm_satisfies_friedmann_I`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdm_satisfies_friedmann_I` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

For positive normalization, vacuum Hubble rate, Newton's constant and time, the squared Hubble rate is the sum of eight pi G times the dust density divided by three and the squared vacuum Hubble rate.

**Theorem 1.22 (Second flat dust and vacuum equation).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdm_satisfies_friedmann_II`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdm_satisfies_friedmann_II` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

Under the same positivity conditions, the normalized second derivative is the squared vacuum Hubble rate minus four pi G times the dust density divided by three.

**Theorem 1.23 (Acceleration onset).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdm_inflection_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdm_inflection_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

For positive normalization, vacuum Hubble rate and time, acceleration is positive exactly when the hyperbolic sine of the scale-factor argument exceeds the reciprocal square root of two.

**Theorem 1.24 (Density parameter acceleration threshold).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdm_density_parameter_acceleration`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdm_density_parameter_acceleration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

For positive normalization, vacuum Hubble rate, Newton's constant and time, acceleration is positive exactly when the matter density parameter is less than twice the vacuum density parameter.

**Definition 1.25 (Matter-to-vacuum density ratio).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdmMatterVacuumRatio`

*Formalization.* `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdmMatterVacuumRatio` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

Cube the ratio of scale normalization to scale factor.

**Theorem 1.26 (Transition scale).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdm_transition_scale`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdm_transition_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

For positive normalization, vacuum Hubble rate and time, acceleration vanishes exactly when the scale factor divided by its normalization equals two to the power minus one third.

**Theorem 1.27 (Unique positive transition time).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdm_transition_time`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdm_transition_time` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

Divide the inverse hyperbolic sine of the reciprocal square root of two by three halves times the vacuum Hubble rate. This gives a positive time, and it is the unique positive time at which acceleration vanishes.

**Theorem 1.28 (Transition redshift).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdm_transition_redshift`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdm_transition_redshift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

At a positive reference time and a positive time of vanishing acceleration, the cube of the reference-to-transition scale ratio equals twice the reciprocal of the matter-to-vacuum density ratio at the reference time.

**Theorem 1.29 (Future Hubble limit).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdm_hubble_tendsto_desitter`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdm_hubble_tendsto_desitter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

For positive normalization and vacuum Hubble rate, the Hubble rate converges to the vacuum Hubble rate as time tends to positive infinity.

**Theorem 1.30 (Finite particle horizon).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.particle_horizon_finite_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.particle_horizon_finite_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

At a positive cutoff time, the inverse power is integrable from the initial singularity exactly when the expansion exponent is below one.

**Theorem 1.31 (Finite event horizon).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.event_horizon_finite_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.event_horizon_finite_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

At a positive cutoff time, the inverse power is integrable to infinite future time exactly when the expansion exponent is above one.

**Theorem 1.32 (Particle horizon distance).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.particle_horizon_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.particle_horizon_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

For expansion exponent below one, the conformal distance is the cutoff raised to one minus the exponent divided by one minus the exponent.

**Theorem 1.33 (Event horizon distance).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.event_horizon_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.event_horizon_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

For expansion exponent above one, the conformal distance is the cutoff raised to one minus the exponent divided by the exponent minus one.

**Theorem 1.34 (Horizon thresholds for the pressure ratio).**

Lean statement: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.flat_horizon_thresholds`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.flat_horizon_thresholds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sean M. Carroll (1997). *Lecture Notes on General Relativity*. URL: <https://arxiv.org/abs/gr-qc/9712019>.

*Commentary.*

For pressure ratio above minus one and a positive cutoff, the particle horizon is finite exactly above minus one third and the event horizon is finite exactly below minus one third.

## References

- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.acceleration_iff_strong_energy_violation`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.continuity_and_friedmann_II_conserve_first_integral`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.deceleration`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.dust_acceleration_iff`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.eosDensity`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.eosDensity_continuity_ode`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.eosDensity_dust_radiation_vacuum`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.event_horizon_finite_iff`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.event_horizon_integral`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.flatDensity`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.flatExponent`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.flatScaleFactor`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.flat_deceleration_thresholds`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.flat_dust_radiation_age`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.flat_horizon_thresholds`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.flat_power_law_deceleration`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.flat_power_law_hubble_age`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.flat_power_law_satisfies_friedmann`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.friedmann_implies_continuity`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.hubble`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdmDensity`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdmMatterVacuumRatio`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdmScaleFactor`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdm_density_parameter_acceleration`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdm_hubble_eq`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdm_hubble_tendsto_desitter`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdm_inflection_iff`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdm_satisfies_friedmann_I`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdm_satisfies_friedmann_II`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdm_transition_redshift`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdm_transition_scale`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.lcdm_transition_time`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.particle_horizon_finite_iff`
- Truth anchor: `D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D.particle_horizon_integral`
