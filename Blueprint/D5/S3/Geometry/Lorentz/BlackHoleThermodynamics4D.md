# Four-dimensional black hole thermodynamics

## Abstract

Kerr-Newman horizon mechanics, rotational extraction, and Schwarzschild heat capacity.

Use geometric units for the Kerr-Newman family with zero magnetic charge. The mass is positive and the sum of squared electric charge and squared spin parameter is at most the squared mass. The Schwarzschild temperature formula restores Newton's constant explicitly.

**Definition 1.1 (Spin parameter).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.spin`

*Formalization.* `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.spin` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

Divide angular momentum by mass.

**Definition 1.2 (Half the horizon separation).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.horizonGap`

*Formalization.* `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.horizonGap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

Take the square root of the difference between squared mass and the sum of squared charge and squared spin parameter.

**Definition 1.3 (Outer radius).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.rPlus`

*Formalization.* `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.rPlus` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

Add the gap to the mass.

**Definition 1.4 (Inner radius).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.rMinus`

*Formalization.* `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.rMinus` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

Subtract the gap from the mass.

**Definition 1.5 (Horizon metric factor).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.horizonFactor`

*Formalization.* `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.horizonFactor` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

Sum the squares of the outer radius and spin parameter.

**Definition 1.6 (Area).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.horizonArea`

*Formalization.* `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.horizonArea` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

Multiply the horizon metric factor by four pi.

**Definition 1.7 (Surface gravity).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.surfaceGravity`

*Formalization.* `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.surfaceGravity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

Divide the horizon separation by twice the horizon metric factor.

**Definition 1.8 (Angular velocity).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.angularVelocity`

*Formalization.* `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.angularVelocity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

Divide the spin parameter by the horizon metric factor.

**Definition 1.9 (Electric potential).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.electricPotential`

*Formalization.* `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.electricPotential` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

Multiply the electric charge by the outer radius and divide by the horizon metric factor.

**Definition 1.10 (Irreducible mass).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.irreducibleMass`

*Formalization.* `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.irreducibleMass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

Take the square root of the horizon area divided by sixteen pi.

**Theorem 1.11 (Positive horizon area).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.horizonArea_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.horizonArea_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

Positive mass makes the outer radius positive, so the metric factor and area are strictly positive.

**Theorem 1.12 (Subextremal surface gravity).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.surfaceGravity_pos_of_subextremal`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.surfaceGravity_pos_of_subextremal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

Positive mass and strictly positive discriminant imply strictly positive surface gravity.

**Theorem 1.13 (Extremal surface gravity).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.surfaceGravity_zero_of_extremal`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.surfaceGravity_zero_of_extremal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

At equality of squared mass and the sum of squared charge and squared spin parameter, the gap and surface gravity vanish.

**Theorem 1.14 (Horizon equation).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.rPlus_sq_add_a_sq_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.rPlus_sq_add_a_sq_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

The metric factor equals twice the product of mass and outer radius minus squared charge for every nonnegative discriminant.

**Definition 1.15 (Squared thermodynamic mass).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerrNewmanMassSq`

*Formalization.* `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerrNewmanMassSq` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

Sum area divided by sixteen pi, half the squared charge, and pi times the sum of fourth power of charge and four times squared angular momentum divided by area.

**Definition 1.16 (Thermodynamic mass).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerrNewmanMass`

*Formalization.* `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerrNewmanMass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

Take the square root of the squared thermodynamic mass.

**Theorem 1.17 (Irreducible mass form).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerrNewmanMassSq_irreducible`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerrNewmanMassSq_irreducible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

For positive area, with irreducible mass m, the squared thermodynamic mass equals the square of m plus charge squared divided by four m, plus angular momentum squared divided by four m squared.

**Theorem 1.18 (Christodoulou-Ruffini identity).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.christodoulou_ruffini_mass_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.christodoulou_ruffini_mass_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

For positive mass and nonnegative discriminant, the rational squared mass evaluated at the horizon area equals the original squared mass. The horizon equation and the angular momentum relation give the corresponding denominator-cleared identity.

**Theorem 1.19 (Mass identification).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerrNewmanMass_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerrNewmanMass_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

Under the same conditions, positivity of the original mass identifies it with the square root of the rational squared mass.

**Theorem 1.20 (First law along curves).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerrNewman_first_law`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerrNewman_first_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

For differentiable area, angular momentum, and charge curves through the thermodynamic coordinates of a positive-mass Kerr-Newman solution with nonnegative discriminant, the mass derivative is the sum of surface gravity times area derivative divided by eight pi, angular velocity times angular momentum derivative, and electric potential times charge derivative. The quotient rule and square root derivative give these coefficients using the horizon equation.

**Theorem 1.21 (Area derivative).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerrNewman_partial_A`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerrNewman_partial_A` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

The mass derivative in area at fixed angular momentum and charge is surface gravity divided by eight pi.

**Theorem 1.22 (Angular momentum derivative).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerrNewman_partial_J`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerrNewman_partial_J` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

The mass derivative in angular momentum at fixed area and charge is the horizon angular velocity.

**Theorem 1.23 (Charge derivative).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerrNewman_partial_Q`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerrNewman_partial_Q` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

The mass derivative in charge at fixed area and angular momentum is the horizon electric potential.

**Theorem 1.24 (Smarr relation).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerrNewman_smarr_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerrNewman_smarr_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

For positive mass and nonnegative discriminant the mass equals surface gravity times area divided by four pi, plus twice angular velocity times angular momentum, plus electric potential times charge.

**Theorem 1.25 (Kerr irreducible mass bounds).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerr_irreducible_mass_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerr_irreducible_mass_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

At zero charge, positive mass and absolute angular momentum at most squared mass imply that the irreducible mass lies between mass divided by square root of two and mass.

**Theorem 1.26 (Sharp lower irreducible mass).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerr_irreducible_mass_min_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerr_irreducible_mass_min_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

Equality with mass divided by square root of two holds exactly when absolute angular momentum equals squared mass.

**Theorem 1.27 (Rotational extraction efficiency).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.penrose_efficiency_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.penrose_efficiency_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

For two Kerr endpoints with positive masses, admissible angular momenta, and nondecreasing horizon area, the fractional mass decrease is at most one minus the reciprocal of square root of two.

**Theorem 1.28 (Sharp extraction efficiency).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.penrose_efficiency_sharp`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.penrose_efficiency_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

An extremal Kerr endpoint and a Schwarzschild endpoint of equal area attain the stated fractional mass decrease.

**Definition 1.29 (Hawking temperature).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.hawkingTemp`

*Formalization.* `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.hawkingTemp` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

Multiply the surface gravity by reduced Planck constant and divide by two pi.

**Definition 1.30 (Bekenstein entropy).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.bekensteinEntropy`

*Formalization.* `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.bekensteinEntropy` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

Divide area by four times Newton's constant times reduced Planck constant.

**Theorem 1.31 (Temperature-entropy differential).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.hawking_entropy_differential`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.hawking_entropy_differential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

For positive Newton and reduced Planck constants, the product of temperature, entropy derivative in area, and area variation equals surface gravity times area variation divided by eight pi times Newton's constant.

**Definition 1.32 (Schwarzschild temperature).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.schwarzschildTemp`

*Formalization.* `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.schwarzschildTemp` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

Divide reduced Planck constant by eight pi times Newton's constant times mass.

**Theorem 1.33 (Schwarzschild specialization).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.hawking_temp_schwarzschild`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.hawking_temp_schwarzschild` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

For positive mass and Newton's constant, the horizon temperature of the nonrotating uncharged solution with geometric mass equal to Newton's constant times mass equals the Schwarzschild temperature.

**Theorem 1.34 (Schwarzschild temperature derivative).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.hawking_temp_schwarzschild_deriv`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.hawking_temp_schwarzschild_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

For positive mass and constants, the derivative is negative reduced Planck constant divided by eight pi times Newton's constant times squared mass, and is strictly negative.

**Definition 1.35 (Mass as a function of temperature).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.schwarzschildMassAtTemp`

*Formalization.* `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.schwarzschildMassAtTemp` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

Divide reduced Planck constant by eight pi times Newton's constant times temperature.

**Theorem 1.36 (Schwarzschild heat capacity).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.schwarzschild_specific_heat_neg`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.schwarzschild_specific_heat_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

For positive mass and constants, the reciprocal-temperature mass branch inverts the Schwarzschild temperature at that mass. Its derivative there equals negative eight pi times Newton's constant times squared mass divided by reduced Planck constant, and is strictly negative.

**Theorem 1.37 (Extremal limit).**

Lean statement: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.extremal_surface_gravity_tendsto_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.extremal_surface_gravity_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Demetrios Christodoulou and Remo Ruffini (1971). *Reversible Transformations of a Charged Black Hole*. DOI: [10.1103/PhysRevD.4.3552](https://doi.org/10.1103/PhysRevD.4.3552). URL: <https://doi.org/10.1103/PhysRevD.4.3552>.

*Commentary.*

At fixed positive mass, convergence of the sum of squared electric charge and squared spin parameter to squared mass implies convergence of surface gravity to zero. The nonnegative horizon gap tends to zero and the denominator stays above squared mass.

## References

- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.angularVelocity`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.bekensteinEntropy`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.christodoulou_ruffini_mass_sq`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.electricPotential`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.extremal_surface_gravity_tendsto_zero`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.hawkingTemp`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.hawking_entropy_differential`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.hawking_temp_schwarzschild`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.hawking_temp_schwarzschild_deriv`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.horizonArea`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.horizonArea_pos`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.horizonFactor`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.horizonGap`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.irreducibleMass`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerrNewmanMass`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerrNewmanMassSq`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerrNewmanMassSq_irreducible`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerrNewmanMass_eq`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerrNewman_first_law`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerrNewman_partial_A`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerrNewman_partial_J`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerrNewman_partial_Q`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerrNewman_smarr_formula`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerr_irreducible_mass_bounds`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.kerr_irreducible_mass_min_iff`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.penrose_efficiency_bound`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.penrose_efficiency_sharp`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.rMinus`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.rPlus`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.rPlus_sq_add_a_sq_eq`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.schwarzschildMassAtTemp`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.schwarzschildTemp`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.schwarzschild_specific_heat_neg`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.spin`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.surfaceGravity`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.surfaceGravity_pos_of_subextremal`
- Truth anchor: `D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D.surfaceGravity_zero_of_extremal`
