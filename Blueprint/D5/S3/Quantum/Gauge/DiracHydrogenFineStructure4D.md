# Relativistic hydrogen and the Coulomb shell algebra

## Abstract

Relativistic hydrogen and the Coulomb shell algebra.

The attractive Coulomb convention uses positive coupling. The circular tower uses a negative signed angular index, with magnitude equal to the principal quantum number. The fine-structure energy depends on the magnitude of the angular index. Expansion uses squared coupling as its real variable near zero.

**Theorem 1.1 (Runge–Lenz bracket decomposition).**

Lean statement: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.runge_lenz_split_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.runge_lenz_split_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C. G. Darwin (1928). *The Wave Equations of the Electron*. DOI: [10.1098/rspa.1928.0076](https://doi.org/10.1098/rspa.1928.0076).

*Commentary.*

The signed angular and Runge–Lenz commutator identities are equivalent to the two rotation brackets and the vanishing mixed bracket of the half-sum and half-difference generators.

**Theorem 1.2 (Coulomb Casimir identities).**

Lean statement: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.runge_lenz_casimir_identities`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.runge_lenz_casimir_identities` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C. G. Darwin (1928). *The Wave Equations of the Electron*. DOI: [10.1098/rspa.1928.0076](https://doi.org/10.1098/rspa.1928.0076).

*Commentary.*

For generator families with each paired angular and Runge–Lenz generator commuting, the sum of their quadratic squares is twice the sum of the two rotation Casimirs. Their mixed product is the difference of the two rotation Casimirs.

**Theorem 1.3 (Casimir and Bohr energy).**

Lean statement: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.bohr_energy_from_casimir`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.bohr_energy_from_casimir` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C. G. Darwin (1928). *The Wave Equations of the Electron*. DOI: [10.1098/rspa.1928.0076](https://doi.org/10.1098/rspa.1928.0076).

*Commentary.*

Equality of the nonnegative spin Casimirs forces equal spin. With the principal index equal to twice that spin plus one, the total Casimir is four times the single spin Casimir and equals the principal index squared minus one, yielding the Bohr denominator.

**Theorem 1.4 (Orbital shell degeneracy).**

Lean statement: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.bohr_shell_degeneracy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.bohr_shell_degeneracy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C. G. Darwin (1928). *The Wave Equations of the Electron*. DOI: [10.1098/rspa.1928.0076](https://doi.org/10.1098/rspa.1928.0076).

*Commentary.*

Summing the odd angular multiplicities below the principal quantum number gives its square.

**Theorem 1.5 (Spin-resolved shell capacity).**

Lean statement: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.bohr_spin_shell_capacity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.bohr_spin_shell_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C. G. Darwin (1928). *The Wave Equations of the Electron*. DOI: [10.1098/rspa.1928.0076](https://doi.org/10.1098/rspa.1928.0076).

*Commentary.*

Doubling the orbital multiplicities gives twice the square of the principal quantum number.

**Theorem 1.6 (Dirac angular subshell count).**

Lean statement: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.dirac_subshell_degeneracy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.dirac_subshell_degeneracy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C. G. Darwin (1928). *The Wave Equations of the Electron*. DOI: [10.1098/rspa.1928.0076](https://doi.org/10.1098/rspa.1928.0076).

*Commentary.*

The angular multiplicities occur twice below the maximal angular index and once at the maximum, giving twice the square of the principal quantum number.

**Theorem 1.7 (Exact circular radial spinors).**

Lean statement: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.dirac_circular_solves_coupled_radial_ode`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.dirac_circular_solves_coupled_radial_ode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C. G. Darwin (1928). *The Wave Equations of the Electron*. DOI: [10.1098/rspa.1928.0076](https://doi.org/10.1098/rspa.1928.0076).

*Commentary.*

At positive radius, positive coupling below the angular index gives the two component derivatives and both signed radial equations at the circular energy.

**Theorem 1.8 (Exact ground radial spinor).**

Lean statement: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.dirac_1s_solves_coupled_radial_ode`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.dirac_1s_solves_coupled_radial_ode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C. G. Darwin (1928). *The Wave Equations of the Electron*. DOI: [10.1098/rspa.1928.0076](https://doi.org/10.1098/rspa.1928.0076).

*Commentary.*

At positive radius, the angular index minus one gives the two derivative and radial identities at the square-root ground energy for coupling between zero and one.

**Theorem 1.9 (Exact first circular excitation).**

Lean statement: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.dirac_2p_solves_coupled_radial_ode`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.dirac_2p_solves_coupled_radial_ode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C. G. Darwin (1928). *The Wave Equations of the Electron*. DOI: [10.1098/rspa.1928.0076](https://doi.org/10.1098/rspa.1928.0076).

*Commentary.*

At positive radius, the angular index minus two gives the two derivative and radial identities for coupling between zero and two.

**Theorem 1.10 (Normalizability and lower-component size).**

Lean statement: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.dirac_1s_normalizable_and_small_component_ratio`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.dirac_1s_normalizable_and_small_component_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C. G. Darwin (1928). *The Wave Equations of the Electron*. DOI: [10.1098/rspa.1928.0076](https://doi.org/10.1098/rspa.1928.0076).

*Commentary.*

For positive mass and coupling between zero and one, the absolute component ratio equals the square-root ratio and is less than one. The sum of squared radial components is integrable on positive radii.

**Theorem 1.11 (Weak-coupling ratio).**

Lean statement: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.dirac_1s_ratio_asymptotic`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.dirac_1s_ratio_asymptotic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C. G. Darwin (1928). *The Wave Equations of the Electron*. DOI: [10.1098/rspa.1928.0076](https://doi.org/10.1098/rspa.1928.0076).

*Commentary.*

The ground-state component ratio divided by the positive coupling tends to one half as the coupling approaches zero.

**Theorem 1.12 (Circular Sommerfeld energy).**

Lean statement: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.sommerfeld_circular_matches_ode`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.sommerfeld_circular_matches_ode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C. G. Darwin (1928). *The Wave Equations of the Electron*. DOI: [10.1098/rspa.1928.0076](https://doi.org/10.1098/rspa.1928.0076).

*Commentary.*

For equal principal and angular indices and positive coupling below the angular index, the Sommerfeld value equals the circular radial eigenvalue.

**Theorem 1.13 (Energy below rest mass).**

Lean statement: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.sommerfeld_bound_state_window`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.sommerfeld_bound_state_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C. G. Darwin (1928). *The Wave Equations of the Electron*. DOI: [10.1098/rspa.1928.0076](https://doi.org/10.1098/rspa.1928.0076).

*Commentary.*

Within the bound-state domain and for positive mass, the Sommerfeld energy is positive and strictly below the rest mass.

**Theorem 1.14 (Critical ground energy).**

Lean statement: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.sommerfeld_ground_critical_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.sommerfeld_ground_critical_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C. G. Darwin (1928). *The Wave Equations of the Electron*. DOI: [10.1098/rspa.1928.0076](https://doi.org/10.1098/rspa.1928.0076).

*Commentary.*

The ground energy tends to zero as the coupling approaches one from below.

**Theorem 1.15 (Angular fine-structure ordering).**

Lean statement: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.sommerfeld_strictly_increasing_in_k`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.sommerfeld_strictly_increasing_in_k` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C. G. Darwin (1928). *The Wave Equations of the Electron*. DOI: [10.1098/rspa.1928.0076](https://doi.org/10.1098/rspa.1928.0076).

*Commentary.*

At fixed principal index and positive mass and coupling in both domains, the energy increases strictly with the angular index.

**Theorem 1.16 (Fourth-order fine structure).**

Lean statement: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.sommerfeld_fourth_order_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.sommerfeld_fourth_order_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C. G. Darwin (1928). *The Wave Equations of the Electron*. DOI: [10.1098/rspa.1928.0076](https://doi.org/10.1098/rspa.1928.0076).

*Commentary.*

The squared-coupling energy at zero equals the rest mass. Its first derivative is the Bohr coefficient, and half of its second derivative is the fine-structure coefficient.

**Theorem 1.17 (Leading two-p splitting).**

Lean statement: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.sommerfeld_2p_splitting_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.sommerfeld_2p_splitting_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C. G. Darwin (1928). *The Wave Equations of the Electron*. DOI: [10.1098/rspa.1928.0076](https://doi.org/10.1098/rspa.1928.0076).

*Commentary.*

Half the difference of the squared-coupling second derivatives at principal index two equals the mass divided by thirty-two.

## References

- Truth anchor: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.bohr_energy_from_casimir`
- Truth anchor: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.bohr_shell_degeneracy`
- Truth anchor: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.bohr_spin_shell_capacity`
- Truth anchor: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.dirac_1s_normalizable_and_small_component_ratio`
- Truth anchor: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.dirac_1s_ratio_asymptotic`
- Truth anchor: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.dirac_1s_solves_coupled_radial_ode`
- Truth anchor: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.dirac_2p_solves_coupled_radial_ode`
- Truth anchor: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.dirac_circular_solves_coupled_radial_ode`
- Truth anchor: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.dirac_subshell_degeneracy`
- Truth anchor: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.runge_lenz_casimir_identities`
- Truth anchor: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.runge_lenz_split_iff`
- Truth anchor: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.sommerfeld_2p_splitting_coefficient`
- Truth anchor: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.sommerfeld_bound_state_window`
- Truth anchor: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.sommerfeld_circular_matches_ode`
- Truth anchor: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.sommerfeld_fourth_order_expansion`
- Truth anchor: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.sommerfeld_ground_critical_limit`
- Truth anchor: `D5/S3/Quantum/Gauge/DiracHydrogenFineStructure4D.sommerfeld_strictly_increasing_in_k`
