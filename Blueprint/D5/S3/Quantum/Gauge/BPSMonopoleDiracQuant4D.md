# Bogomolny monopoles, dyons and electric–magnetic duality

## Abstract

Pointwise dyon energy, the radial monopole mass, and the modular charge action.

The electric, magnetic and scalar-gradient fields take values in finite Euclidean coordinates. In the radial monopole, the magnetic and Higgs-gradient terms yield a boundary contribution. The dyon mass uses the central charge and the imaginary part of the complex coupling.

**Theorem 1.1 (Dyon square completion).**

Lean statement: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.bogomolny_dyon_completion`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.bogomolny_dyon_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. K. Prasad and C. M. Sommerfield (1975). *Exact Classical Solution for the 't Hooft Monopole and the Julia-Zee Dyon*. DOI: [10.1103/PhysRevLett.35.760](https://doi.org/10.1103/PhysRevLett.35.760). URL: <https://doi.org/10.1103/PhysRevLett.35.760>.

*Commentary.*

For each real angle, the energy is the sum of two half squared norms and the electric and magnetic pairings weighted by sine and cosine.

**Theorem 1.2 (Dyon energy bound).**

Lean statement: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.bogomolny_dyon_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.bogomolny_dyon_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. K. Prasad and C. M. Sommerfield (1975). *Exact Classical Solution for the 't Hooft Monopole and the Julia-Zee Dyon*. DOI: [10.1103/PhysRevLett.35.760](https://doi.org/10.1103/PhysRevLett.35.760). URL: <https://doi.org/10.1103/PhysRevLett.35.760>.

*Commentary.*

The Euclidean norm of the electric and magnetic pairings is a lower bound for the energy.

**Theorem 1.3 (Dyon equality criterion).**

Lean statement: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.bogomolny_dyon_saturation_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.bogomolny_dyon_saturation_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. K. Prasad and C. M. Sommerfield (1975). *Exact Classical Solution for the 't Hooft Monopole and the Julia-Zee Dyon*. DOI: [10.1103/PhysRevLett.35.760](https://doi.org/10.1103/PhysRevLett.35.760). URL: <https://doi.org/10.1103/PhysRevLett.35.760>.

*Commentary.*

Equality holds exactly when a real angle aligns the electric and magnetic fields with the scalar gradient and gives a nonnegative weighted pairing.

**Theorem 1.4 (Magnetic energy and equality).**

Lean statement: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.bogomolny_monopole_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.bogomolny_monopole_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. K. Prasad and C. M. Sommerfield (1975). *Exact Classical Solution for the 't Hooft Monopole and the Julia-Zee Dyon*. DOI: [10.1103/PhysRevLett.35.760](https://doi.org/10.1103/PhysRevLett.35.760). URL: <https://doi.org/10.1103/PhysRevLett.35.760>.

*Commentary.*

With zero electric field the absolute magnetic pairing bounds the energy from below. Equality holds precisely when the magnetic field equals either sign of the scalar gradient.

**Theorem 1.5 (Prasad–Sommerfield equations).**

Lean statement: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.ps_solves_bogomolny_ode`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.ps_solves_bogomolny_ode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. K. Prasad and C. M. Sommerfield (1975). *Exact Classical Solution for the 't Hooft Monopole and the Julia-Zee Dyon*. DOI: [10.1103/PhysRevLett.35.760](https://doi.org/10.1103/PhysRevLett.35.760). URL: <https://doi.org/10.1103/PhysRevLett.35.760>.

*Commentary.*

At positive radius the derivative of K is minus K times H divided by the radius. The radius times the derivative of H minus H equals one minus K squared.

**Theorem 1.6 (Energy density as a radial derivative).**

Lean statement: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.ps_radial_energy_exact_deriv`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.ps_radial_energy_exact_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. K. Prasad and C. M. Sommerfield (1975). *Exact Classical Solution for the 't Hooft Monopole and the Julia-Zee Dyon*. DOI: [10.1103/PhysRevLett.35.760](https://doi.org/10.1103/PhysRevLett.35.760). URL: <https://doi.org/10.1103/PhysRevLett.35.760>.

*Commentary.*

The normalized energy is the sum of the squared derivative of K, the magnetic radial square, the scalar radial square using the radius times the derivative of H minus H, and the scalar angular square.

**Theorem 1.7 (Radial Bogomolny boundary term).**

Lean statement: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.ps_total_deriv`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.ps_total_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. K. Prasad and C. M. Sommerfield (1975). *Exact Classical Solution for the 't Hooft Monopole and the Julia-Zee Dyon*. DOI: [10.1103/PhysRevLett.35.760](https://doi.org/10.1103/PhysRevLett.35.760). URL: <https://doi.org/10.1103/PhysRevLett.35.760>.

*Commentary.*

The radial equations turn the magnetic and Higgs-gradient energy into the derivative of the boundary expression.

**Theorem 1.8 (Endpoint limits).**

Lean statement: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.ps_origin_and_infinity_limits`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.ps_origin_and_infinity_limits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. K. Prasad and C. M. Sommerfield (1975). *Exact Classical Solution for the 't Hooft Monopole and the Julia-Zee Dyon*. DOI: [10.1103/PhysRevLett.35.760](https://doi.org/10.1103/PhysRevLett.35.760). URL: <https://doi.org/10.1103/PhysRevLett.35.760>.

*Commentary.*

The boundary expression tends to zero from the right at the origin and to one at positive infinity.

**Theorem 1.9 (Exact normalized integral and monopole mass).**

Lean statement: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.ps_monopole_exact_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.ps_monopole_exact_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. K. Prasad and C. M. Sommerfield (1975). *Exact Classical Solution for the 't Hooft Monopole and the Julia-Zee Dyon*. DOI: [10.1103/PhysRevLett.35.760](https://doi.org/10.1103/PhysRevLett.35.760). URL: <https://doi.org/10.1103/PhysRevLett.35.760>.

*Commentary.*

The radial energy is integrable on the positive half-line and has integral one. At positive vacuum value and gauge coupling, the mass is four pi times the vacuum value divided by the coupling.

**Theorem 1.10 (Charge pairing and field angular momentum).**

Lean statement: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.dsz_half_integer_angMom_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.dsz_half_integer_angMom_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. K. Prasad and C. M. Sommerfield (1975). *Exact Classical Solution for the 't Hooft Monopole and the Julia-Zee Dyon*. DOI: [10.1103/PhysRevLett.35.760](https://doi.org/10.1103/PhysRevLett.35.760). URL: <https://doi.org/10.1103/PhysRevLett.35.760>.

*Commentary.*

The alternating charge pairing is an integer multiple of two pi exactly when the corresponding field angular momentum is a half-integer.

**Theorem 1.11 (Electric charge lattice).**

Lean statement: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.dirac_charge_quantization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.dirac_charge_quantization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. K. Prasad and C. M. Sommerfield (1975). *Exact Classical Solution for the 't Hooft Monopole and the Julia-Zee Dyon*. DOI: [10.1103/PhysRevLett.35.760](https://doi.org/10.1103/PhysRevLett.35.760). URL: <https://doi.org/10.1103/PhysRevLett.35.760>.

*Commentary.*

Pairing with a pure monopole of nonzero magnetic charge places any electric charge satisfying the quantization condition in the lattice generated by two pi divided by the magnetic charge.

**Theorem 1.12 (Action on the charge lattice).**

Lean statement: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.sl2z_charge_action`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.sl2z_charge_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. K. Prasad and C. M. Sommerfield (1975). *Exact Classical Solution for the 't Hooft Monopole and the Julia-Zee Dyon*. DOI: [10.1103/PhysRevLett.35.760](https://doi.org/10.1103/PhysRevLett.35.760). URL: <https://doi.org/10.1103/PhysRevLett.35.760>.

*Commentary.*

The identity leaves every charge unchanged, and the charge transforms for a matrix product compose in order.

**Theorem 1.13 (Invariant lattice pairing).**

Lean statement: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.dsz_pairing_sl2z_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.dsz_pairing_sl2z_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. K. Prasad and C. M. Sommerfield (1975). *Exact Classical Solution for the 't Hooft Monopole and the Julia-Zee Dyon*. DOI: [10.1103/PhysRevLett.35.760](https://doi.org/10.1103/PhysRevLett.35.760). URL: <https://doi.org/10.1103/PhysRevLett.35.760>.

*Commentary.*

Simultaneous determinant-one integer transformations preserve the alternating pairing of two charges.

**Theorem 1.14 (Modular transformation of the coupling).**

Lean statement: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.sl2z_preserves_upper_half_plane`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.sl2z_preserves_upper_half_plane` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. K. Prasad and C. M. Sommerfield (1975). *Exact Classical Solution for the 't Hooft Monopole and the Julia-Zee Dyon*. DOI: [10.1103/PhysRevLett.35.760](https://doi.org/10.1103/PhysRevLett.35.760). URL: <https://doi.org/10.1103/PhysRevLett.35.760>.

*Commentary.*

The transformed imaginary part is the original imaginary part divided by the norm squared of the Möbius denominator. Thus a coupling in the upper half-plane stays there.

**Theorem 1.15 (Modular invariance of the dyon mass).**

Lean statement: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.bpsDyonMass_sl2z_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.bpsDyonMass_sl2z_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. K. Prasad and C. M. Sommerfield (1975). *Exact Classical Solution for the 't Hooft Monopole and the Julia-Zee Dyon*. DOI: [10.1103/PhysRevLett.35.760](https://doi.org/10.1103/PhysRevLett.35.760). URL: <https://doi.org/10.1103/PhysRevLett.35.760>.

*Commentary.*

The charge transform divides the central charge by the same factor whose norm rescales the square root of the imaginary part. The ratio remains invariant.

**Theorem 1.16 (Electric–magnetic exchange).**

Lean statement: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.bpsDyonMass_S_duality`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.bpsDyonMass_S_duality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. K. Prasad and C. M. Sommerfield (1975). *Exact Classical Solution for the 't Hooft Monopole and the Julia-Zee Dyon*. DOI: [10.1103/PhysRevLett.35.760](https://doi.org/10.1103/PhysRevLett.35.760). URL: <https://doi.org/10.1103/PhysRevLett.35.760>.

*Commentary.*

Inversion with a minus sign exchanges the charge components and negates the original electric component, preserving the mass.

**Theorem 1.17 (Integer shift of the coupling).**

Lean statement: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.bpsDyonMass_T_duality`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.bpsDyonMass_T_duality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. K. Prasad and C. M. Sommerfield (1975). *Exact Classical Solution for the 't Hooft Monopole and the Julia-Zee Dyon*. DOI: [10.1103/PhysRevLett.35.760](https://doi.org/10.1103/PhysRevLett.35.760). URL: <https://doi.org/10.1103/PhysRevLett.35.760>.

*Commentary.*

Adding one to the coupling subtracts the magnetic charge from the electric charge, preserving the mass.

**Theorem 1.18 (Inversion of the gauge coupling).**

Lean statement: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.sl2z_weak_strong_coupling`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.sl2z_weak_strong_coupling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. K. Prasad and C. M. Sommerfield (1975). *Exact Classical Solution for the 't Hooft Monopole and the Julia-Zee Dyon*. DOI: [10.1103/PhysRevLett.35.760](https://doi.org/10.1103/PhysRevLett.35.760). URL: <https://doi.org/10.1103/PhysRevLett.35.760>.

*Commentary.*

On the positive imaginary axis, modular inversion replaces a positive gauge coupling by four pi divided by that coupling.

## References

- Truth anchor: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.bogomolny_dyon_completion`
- Truth anchor: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.bogomolny_dyon_lower_bound`
- Truth anchor: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.bogomolny_dyon_saturation_iff`
- Truth anchor: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.bogomolny_monopole_bound`
- Truth anchor: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.bpsDyonMass_S_duality`
- Truth anchor: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.bpsDyonMass_T_duality`
- Truth anchor: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.bpsDyonMass_sl2z_invariant`
- Truth anchor: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.dirac_charge_quantization`
- Truth anchor: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.dsz_half_integer_angMom_iff`
- Truth anchor: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.dsz_pairing_sl2z_invariant`
- Truth anchor: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.ps_monopole_exact_mass`
- Truth anchor: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.ps_origin_and_infinity_limits`
- Truth anchor: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.ps_radial_energy_exact_deriv`
- Truth anchor: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.ps_solves_bogomolny_ode`
- Truth anchor: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.ps_total_deriv`
- Truth anchor: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.sl2z_charge_action`
- Truth anchor: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.sl2z_preserves_upper_half_plane`
- Truth anchor: `D5/S3/Quantum/Gauge/BPSMonopoleDiracQuant4D.sl2z_weak_strong_coupling`
