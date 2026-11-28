# Hawking and Unruh thermal radiation in four dimensions

## Abstract

Horizon periodicity, thermal moments, and entropy production in a four-dimensional blackbody evaporation model.

The leading Euclidean polar metric fixes the thermal period by the circumference-to-radius test. Detailed balance gives the bosonic and fermionic occupation numbers. In the Schwarzschild blackbody model, the spectral moments set the power scale and the mass-loss and entropy laws determine the complete evaporation trajectory.

**Definition 1.1 (Euclidean time orbit length).**

Lean statement: `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.euclideanCircumference`

*Formalization.* `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.euclideanCircumference` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* G. W. Gibbons and S. W. Hawking (1977). *Action integrals and partition functions in quantum gravity*. DOI: [10.1103/PhysRevD.15.2752](https://doi.org/10.1103/PhysRevD.15.2752). URL: <https://doi.org/10.1103/PhysRevD.15.2752>.

*Commentary.*

Integrate the speed of the fixed-radius circular orbit over one Euclidean period.

**Theorem 1.2 (Euclidean period and horizon temperature).**

Lean statement: `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.gibbons_hawking_conical_periodicity`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.gibbons_hawking_conical_periodicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. W. Gibbons and S. W. Hawking (1977). *Action integrals and partition functions in quantum gravity*. DOI: [10.1103/PhysRevD.15.2752](https://doi.org/10.1103/PhysRevD.15.2752). URL: <https://doi.org/10.1103/PhysRevD.15.2752>.

*Commentary.*

For positive surface gravity, Euclidean period, and radius, the circumference divided by twice pi times the radius is the product of gravity and period divided by twice pi. The ratio is one exactly at the period twice pi over surface gravity. Its reciprocal is the Hawking temperature in natural units, with acceleration as the Unruh parameter and inverse eight pi times the mass in Schwarzschild.

**Theorem 1.3 (Bose and Fermi detailed balance).**

Lean statement: `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.bogoliubov_planck_and_fermi_dirac_spectra`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.bogoliubov_planck_and_fermi_dirac_spectra` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. W. Gibbons and S. W. Hawking (1977). *Action integrals and partition functions in quantum gravity*. DOI: [10.1103/PhysRevD.15.2752](https://doi.org/10.1103/PhysRevD.15.2752). URL: <https://doi.org/10.1103/PhysRevD.15.2752>.

*Commentary.*

For positive inverse temperature and frequency, write E for the exponential of their product and set A equal to E times B. Bosonic normalization fixes A minus B to one, so A equals one plus B and the numerators E and one have denominator E minus one. Fermionic normalization fixes A plus B to one, so A equals one minus B and the same numerators have denominator E plus one. The bosonic occupation is positive. The fermionic occupation lies strictly between zero and one half, and its complement agrees with the modular KMS symbol. Dividing the occupation by one plus B for bosons and by one minus B for fermions gives the reciprocal of E. Frequency times the bosonic occupation tends to the reciprocal inverse temperature at zero from above, and E times that occupation tends to one at infinite frequency.

**Theorem 1.4 (Bose and Fermi cubic moments).**

Lean statement: `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.stefan_boltzmann_4d_bose_and_fermi_integrals`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.stefan_boltzmann_4d_bose_and_fermi_integrals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. W. Gibbons and S. W. Hawking (1977). *Action integrals and partition functions in quantum gravity*. DOI: [10.1103/PhysRevD.15.2752](https://doi.org/10.1103/PhysRevD.15.2752). URL: <https://doi.org/10.1103/PhysRevD.15.2752>.

*Commentary.*

The cubic Bose integral on the positive real half-line is pi to the fourth power divided by fifteen. The geometric expansion of the occupation number permits termwise integration of nonnegative functions. The Fermi integral is seven eighths of the Bose integral because subtracting twice the Bose integrand with doubled exponential argument introduces a factor of one sixteenth after rescaling.

**Definition 1.5 (Flux coefficient for one bosonic helicity).**

Lean statement: `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.bosonicStefanBoltzmann`

*Formalization.* `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.bosonicStefanBoltzmann` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* G. W. Gibbons and S. W. Hawking (1977). *Action integrals and partition functions in quantum gravity*. DOI: [10.1103/PhysRevD.15.2752](https://doi.org/10.1103/PhysRevD.15.2752). URL: <https://doi.org/10.1103/PhysRevD.15.2752>.

*Commentary.*

Divide the cubic Bose moment by eight pi squared.

**Definition 1.6 (Blackbody luminosity).**

Lean statement: `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.hawkingLuminosity`

*Formalization.* `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.hawkingLuminosity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* G. W. Gibbons and S. W. Hawking (1977). *Action integrals and partition functions in quantum gravity*. DOI: [10.1103/PhysRevD.15.2752](https://doi.org/10.1103/PhysRevD.15.2752). URL: <https://doi.org/10.1103/PhysRevD.15.2752>.

*Commentary.*

Multiply the effective helicity count and the single-helicity flux coefficient by the horizon area and fourth power of the Schwarzschild temperature.

**Theorem 1.7 (Schwarzschild inverse-square luminosity).**

Lean statement: `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.hawking_luminosity_inverse_square_law`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.hawking_luminosity_inverse_square_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. W. Gibbons and S. W. Hawking (1977). *Action integrals and partition functions in quantum gravity*. DOI: [10.1103/PhysRevD.15.2752](https://doi.org/10.1103/PhysRevD.15.2752). URL: <https://doi.org/10.1103/PhysRevD.15.2752>.

*Commentary.*

At positive mass the horizon area times the fourth power of the temperature gives an inverse-square mass law. With the single-helicity thermal coefficient, the result is the effective helicity count divided by thirty thousand seven hundred twenty times pi and the squared mass.

**Definition 1.8 (Evaporation time).**

Lean statement: `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.evapTime`

*Formalization.* `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.evapTime` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* G. W. Gibbons and S. W. Hawking (1977). *Action integrals and partition functions in quantum gravity*. DOI: [10.1103/PhysRevD.15.2752](https://doi.org/10.1103/PhysRevD.15.2752). URL: <https://doi.org/10.1103/PhysRevD.15.2752>.

*Commentary.*

The lifetime is the initial mass cubed divided by three times the evaporation coefficient.

**Definition 1.9 (Mass along the trajectory).**

Lean statement: `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.evapMass`

*Formalization.* `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.evapMass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* G. W. Gibbons and S. W. Hawking (1977). *Action integrals and partition functions in quantum gravity*. DOI: [10.1103/PhysRevD.15.2752](https://doi.org/10.1103/PhysRevD.15.2752). URL: <https://doi.org/10.1103/PhysRevD.15.2752>.

*Commentary.*

Multiply the initial mass by the cube root of one minus the elapsed fraction of the lifetime.

**Theorem 1.10 (Evaporation and increasing temperature).**

Lean statement: `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.hawking_evaporation_trajectory_and_runaway_heating`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.hawking_evaporation_trajectory_and_runaway_heating` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. W. Gibbons and S. W. Hawking (1977). *Action integrals and partition functions in quantum gravity*. DOI: [10.1103/PhysRevD.15.2752](https://doi.org/10.1103/PhysRevD.15.2752). URL: <https://doi.org/10.1103/PhysRevD.15.2752>.

*Commentary.*

For positive initial mass and evaporation coefficient, the evaporation time is the cubed initial mass divided by three times the coefficient. The mass starts at the initial mass and is positive before the endpoint. Its derivative is minus the evaporation coefficient divided by squared instantaneous mass. At the endpoint the mass tends to zero from the left and the temperature tends to positive infinity.

**Definition 1.11 (Radiation entropy flux).**

Lean statement: `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.radiationEntropyFlux`

*Formalization.* `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.radiationEntropyFlux` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* G. W. Gibbons and S. W. Hawking (1977). *Action integrals and partition functions in quantum gravity*. DOI: [10.1103/PhysRevD.15.2752](https://doi.org/10.1103/PhysRevD.15.2752). URL: <https://doi.org/10.1103/PhysRevD.15.2752>.

*Commentary.*

The enthalpy flux is the power plus one third of the power. Dividing it by the radiation temperature gives the entropy flux.

**Definition 1.12 (Power in the evaporation equation).**

Lean statement: `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.hawkingPower`

*Formalization.* `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.hawkingPower` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* G. W. Gibbons and S. W. Hawking (1977). *Action integrals and partition functions in quantum gravity*. DOI: [10.1103/PhysRevD.15.2752](https://doi.org/10.1103/PhysRevD.15.2752). URL: <https://doi.org/10.1103/PhysRevD.15.2752>.

*Commentary.*

Divide the evaporation coefficient by the squared instantaneous mass.

**Definition 1.13 (Schwarzschild horizon entropy).**

Lean statement: `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.schwarzschildEntropy`

*Formalization.* `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.schwarzschildEntropy` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* G. W. Gibbons and S. W. Hawking (1977). *Action integrals and partition functions in quantum gravity*. DOI: [10.1103/PhysRevD.15.2752](https://doi.org/10.1103/PhysRevD.15.2752). URL: <https://doi.org/10.1103/PhysRevD.15.2752>.

*Commentary.*

Use the Bekenstein–Hawking formula in natural units with vanishing charge and angular momentum.

**Definition 1.14 (Entropy flux along the evaporation trajectory).**

Lean statement: `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.evaporationEntropyFlux`

*Formalization.* `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.evaporationEntropyFlux` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* G. W. Gibbons and S. W. Hawking (1977). *Action integrals and partition functions in quantum gravity*. DOI: [10.1103/PhysRevD.15.2752](https://doi.org/10.1103/PhysRevD.15.2752). URL: <https://doi.org/10.1103/PhysRevD.15.2752>.

*Commentary.*

Evaluate the radiation entropy flux at the power and temperature of the instantaneous Schwarzschild mass.

**Theorem 1.15 (Exact entropy production).**

Lean statement: `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.zurek_generalized_second_law_irreversible_entropy_production`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.zurek_generalized_second_law_irreversible_entropy_production` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. W. Gibbons and S. W. Hawking (1977). *Action integrals and partition functions in quantum gravity*. DOI: [10.1103/PhysRevD.15.2752](https://doi.org/10.1103/PhysRevD.15.2752). URL: <https://doi.org/10.1103/PhysRevD.15.2752>.

*Commentary.*

For positive initial mass and evaporation coefficient, from time zero up to the lifetime endpoint, the horizon entropy is four pi times the squared mass. Its derivative is minus the emitted power divided by temperature, equal to minus eight pi times the evaporation coefficient divided by the mass. With pressure one third of the energy density the ideal thermal radiation carries four thirds of the positive power-to-temperature ratio. The generalized rate is one third of this ratio, equal to eight pi times the evaporation coefficient divided by three times the instantaneous mass. The flux is integrable at the endpoint. Its lifetime integral is four thirds of the initial horizon entropy, leaving a positive net increase of one third of the initial horizon entropy.

## References

- Truth anchor: `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.bogoliubov_planck_and_fermi_dirac_spectra`
- Truth anchor: `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.bosonicStefanBoltzmann`
- Truth anchor: `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.euclideanCircumference`
- Truth anchor: `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.evapMass`
- Truth anchor: `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.evapTime`
- Truth anchor: `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.evaporationEntropyFlux`
- Truth anchor: `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.gibbons_hawking_conical_periodicity`
- Truth anchor: `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.hawkingLuminosity`
- Truth anchor: `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.hawkingPower`
- Truth anchor: `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.hawking_evaporation_trajectory_and_runaway_heating`
- Truth anchor: `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.hawking_luminosity_inverse_square_law`
- Truth anchor: `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.radiationEntropyFlux`
- Truth anchor: `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.schwarzschildEntropy`
- Truth anchor: `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.stefan_boltzmann_4d_bose_and_fermi_integrals`
- Truth anchor: `D5/S3/Geometry/Lorentz/HawkingUnruhThermalRadiation4D.zurek_generalized_second_law_irreversible_entropy_production`
- Dependency: [D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D](BlackHoleThermodynamics4D.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness](../../Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness.md)
