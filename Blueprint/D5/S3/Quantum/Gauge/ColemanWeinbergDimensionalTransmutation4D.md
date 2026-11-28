# Coleman–Weinberg dimensional transmutation in four dimensions

## Abstract

Fourth-derivative renormalization, dimensional transmutation, and stability for a one-loop scalar potential.

A logarithmic quartic correction to the massless scalar potential selects a positive field scale. The same correction fixes the curvature at the minima and determines whether the potential is bounded below. The scale invariance here refers to changing the renormalization point while running the quartic at fixed logarithmic coefficient.

**Definition 1.1 (Scalar electrodynamics coefficient).**

Lean statement: `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cwCoeff`

*Formalization.* `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cwCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sidney Coleman and Erick Weinberg (1973). *Radiative Corrections as the Origin of Spontaneous Symmetry Breaking*. DOI: [10.1103/PhysRevD.7.1888](https://doi.org/10.1103/PhysRevD.7.1888). URL: <https://doi.org/10.1103/PhysRevD.7.1888>.

*Commentary.*

The logarithmic coefficient is three times the fourth power of the electric coupling divided by sixty-four times pi squared.

**Definition 1.2 (Renormalized one-loop potential).**

Lean statement: `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cwPotential`

*Formalization.* `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cwPotential` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sidney Coleman and Erick Weinberg (1973). *Radiative Corrections as the Origin of Spontaneous Symmetry Breaking*. DOI: [10.1103/PhysRevD.7.1888](https://doi.org/10.1103/PhysRevD.7.1888). URL: <https://doi.org/10.1103/PhysRevD.7.1888>.

*Commentary.*

The classical coefficient is the quartic coupling divided by twenty-four. The correction is the logarithmic coefficient times the fourth power of the field times the logarithm of the squared field-to-scale ratio minus twenty-five sixths.

**Definition 1.3 (Potential expressed at its vacuum scale).**

Lean statement: `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cwUniversal`

*Formalization.* `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cwUniversal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sidney Coleman and Erick Weinberg (1973). *Radiative Corrections as the Origin of Spontaneous Symmetry Breaking*. DOI: [10.1103/PhysRevD.7.1888](https://doi.org/10.1103/PhysRevD.7.1888). URL: <https://doi.org/10.1103/PhysRevD.7.1888>.

*Commentary.*

Multiply the logarithmic coefficient and the fourth power of the field by the logarithm of the squared field-to-vacuum ratio minus one half.

**Definition 1.4 (Transmuted scale).**

Lean statement: `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cwVev`

*Formalization.* `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cwVev` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sidney Coleman and Erick Weinberg (1973). *Radiative Corrections as the Origin of Spontaneous Symmetry Breaking*. DOI: [10.1103/PhysRevD.7.1888](https://doi.org/10.1103/PhysRevD.7.1888). URL: <https://doi.org/10.1103/PhysRevD.7.1888>.

*Commentary.*

Multiply the renormalization scale by the exponential of eleven sixths minus the quartic coupling divided by forty-eight times the logarithmic coefficient.

**Definition 1.5 (Running quartic at fixed logarithmic coefficient).**

Lean statement: `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cwRunningLam`

*Formalization.* `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cwRunningLam` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sidney Coleman and Erick Weinberg (1973). *Radiative Corrections as the Origin of Spontaneous Symmetry Breaking*. DOI: [10.1103/PhysRevD.7.1888](https://doi.org/10.1103/PhysRevD.7.1888). URL: <https://doi.org/10.1103/PhysRevD.7.1888>.

*Commentary.*

Add forty-eight times the logarithmic coefficient times the logarithm of the scale-to-reference ratio to the reference quartic.

**Definition 1.6 (Gauge and Yukawa coefficient).**

Lean statement: `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cwEffCoeff`

*Formalization.* `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cwEffCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sidney Coleman and Erick Weinberg (1973). *Radiative Corrections as the Origin of Spontaneous Symmetry Breaking*. DOI: [10.1103/PhysRevD.7.1888](https://doi.org/10.1103/PhysRevD.7.1888). URL: <https://doi.org/10.1103/PhysRevD.7.1888>.

*Commentary.*

Subtract four times the color multiplicity times the fourth power of the Yukawa coupling from three times the fourth power of the gauge coupling, then divide by sixty-four times pi squared.

**Theorem 1.7 (Fourth-derivative renormalization).**

Lean statement: `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cw_fourth_derivative_renormalization_condition`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cw_fourth_derivative_renormalization_condition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sidney Coleman and Erick Weinberg (1973). *Radiative Corrections as the Origin of Spontaneous Symmetry Breaking*. DOI: [10.1103/PhysRevD.7.1888](https://doi.org/10.1103/PhysRevD.7.1888). URL: <https://doi.org/10.1103/PhysRevD.7.1888>.

*Commentary.*

At a positive renormalization field, the fourth derivative of the logarithmic quartic is one hundred and that of its subtracted form is zero. The full fourth derivative is the prescribed quartic coupling. For a nonzero correction coefficient, a constant subtraction has this property exactly when it is twenty-five sixths.

**Theorem 1.8 (Dimensional transmutation and the quartic coupling).**

Lean statement: `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cw_dimensional_transmutation_and_coupling_lock`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cw_dimensional_transmutation_and_coupling_lock` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sidney Coleman and Erick Weinberg (1973). *Radiative Corrections as the Origin of Spontaneous Symmetry Breaking*. DOI: [10.1103/PhysRevD.7.1888](https://doi.org/10.1103/PhysRevD.7.1888). URL: <https://doi.org/10.1103/PhysRevD.7.1888>.

*Commentary.*

For positive logarithmic coefficient and renormalization scale, the transmuted scale is positive. The two potential expressions agree at every real field and the potential is continuous at zero. The renormalization scale is the vacuum scale exactly when the quartic equals eighty-eight times the logarithmic coefficient, which in scalar electrodynamics is thirty-three times the fourth power of the gauge coupling divided by eight pi squared.

**Theorem 1.9 (Two global minima).**

Lean statement: `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cw_radiative_global_minimum_and_symmetry_breaking`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cw_radiative_global_minimum_and_symmetry_breaking` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sidney Coleman and Erick Weinberg (1973). *Radiative Corrections as the Origin of Spontaneous Symmetry Breaking*. DOI: [10.1103/PhysRevD.7.1888](https://doi.org/10.1103/PhysRevD.7.1888). URL: <https://doi.org/10.1103/PhysRevD.7.1888>.

*Commentary.*

For positive coefficient and vacuum scale the derivative is four times the coefficient, the cubed field, and the logarithm of the squared field-to-vacuum ratio, including derivative zero at the origin. The global minimum on the real line is attained exactly at the two signed vacuum fields. Its value is minus half the coefficient times the fourth power of the vacuum scale and lies strictly below the value zero at the origin.

**Theorem 1.10 (Curvature and mass ratio).**

Lean statement: `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cw_radiative_scalar_to_vector_mass_ratio`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cw_radiative_scalar_to_vector_mass_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sidney Coleman and Erick Weinberg (1973). *Radiative Corrections as the Origin of Spontaneous Symmetry Breaking*. DOI: [10.1103/PhysRevD.7.1888](https://doi.org/10.1103/PhysRevD.7.1888). URL: <https://doi.org/10.1103/PhysRevD.7.1888>.

*Commentary.*

For positive logarithmic coefficient, vacuum scale, and electric coupling, the derivative of the potential derivative at the vacuum is eight times the coefficient and the squared vacuum scale, which is positive. The charged mass formula of the Higgs module evaluated at twice the scalar-electrodynamics coupling gives the squared vector mass. At the scalar-electrodynamics coefficient, the squared mass ratio is three times the squared electric coupling divided by eight pi squared, equivalently three times the fine-structure constant divided by twice pi.

**Theorem 1.11 (Exact invariance under quartic running).**

Lean statement: `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cw_callan_symanzik_rg_invariance`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cw_callan_symanzik_rg_invariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sidney Coleman and Erick Weinberg (1973). *Radiative Corrections as the Origin of Spontaneous Symmetry Breaking*. DOI: [10.1103/PhysRevD.7.1888](https://doi.org/10.1103/PhysRevD.7.1888). URL: <https://doi.org/10.1103/PhysRevD.7.1888>.

*Commentary.*

For positive coefficient and scales, the scale times the derivative of the running quartic is forty-eight times the coefficient, reducing to nine times the fourth power of the electric coupling divided by four pi squared in scalar electrodynamics. Substituting the running quartic preserves the transmuted scale and the potential at every real field.

**Theorem 1.12 (Strict gauge–Yukawa threshold).**

Lean statement: `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cw_yukawa_vacuum_stability_threshold`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cw_yukawa_vacuum_stability_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sidney Coleman and Erick Weinberg (1973). *Radiative Corrections as the Origin of Spontaneous Symmetry Breaking*. DOI: [10.1103/PhysRevD.7.1888](https://doi.org/10.1103/PhysRevD.7.1888). URL: <https://doi.org/10.1103/PhysRevD.7.1888>.

*Commentary.*

The effective coefficient is positive exactly when four times the color multiplicity times the fourth power of the Yukawa coupling is less than three times the fourth power of the gauge coupling. At a positive renormalization scale, a positive coefficient gives a bounded-below potential tending to positive infinity with the field, and a negative coefficient gives a potential tending to negative infinity.

## References

- Truth anchor: `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cwCoeff`
- Truth anchor: `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cwEffCoeff`
- Truth anchor: `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cwPotential`
- Truth anchor: `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cwRunningLam`
- Truth anchor: `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cwUniversal`
- Truth anchor: `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cwVev`
- Truth anchor: `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cw_callan_symanzik_rg_invariance`
- Truth anchor: `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cw_dimensional_transmutation_and_coupling_lock`
- Truth anchor: `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cw_fourth_derivative_renormalization_condition`
- Truth anchor: `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cw_radiative_global_minimum_and_symmetry_breaking`
- Truth anchor: `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cw_radiative_scalar_to_vector_mass_ratio`
- Truth anchor: `D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D.cw_yukawa_vacuum_stability_threshold`
- Dependency: [D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D](ElectroweakHiggsMechanism4D.md)
- Dependency: [D5/S3/Quantum/Gauge/GaugeUnificationRG4D](GaugeUnificationRG4D.md)
