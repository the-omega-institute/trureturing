# Four-dimensional Wilson lattice gauge theory

## Abstract

Gauge invariance, Osterwalder–Schrader positivity, positive transfer, and the strong-coupling area law in four-dimensional Wilson lattice gauge theory.

The open four-dimensional box consists of two copies of a half-box and a temporal seam. Each copy uses distance from the seam as its time coordinate. The gauge representation is finite dimensional, unitary and measurable.

**Theorem 1.1 (Local gauge invariance of plaquette weights).**

Lean statement: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_plaquette_gauge_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_plaquette_gauge_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Konrad Osterwalder and Erhard Seiler (1978). *Gauge Field Theories on a Lattice*. DOI: [10.1016/0003-4916(78)90039-8](https://doi.org/10.1016/0003-4916(78)90039-8). URL: <https://doi.org/10.1016/0003-4916(78)90039-8>.

*Commentary.*

In an interior plaquette, the endpoint factors from the four link transformations cancel at each intermediate vertex. The residual conjugation leaves the trace and its real part unchanged.

**Theorem 1.2 (Gauge invariance at the seam).**

Lean statement: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_seam_plaquette_gauge_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_seam_plaquette_gauge_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Konrad Osterwalder and Erhard Seiler (1978). *Gauge Field Theories on a Lattice*. DOI: [10.1016/0003-4916(78)90039-8](https://doi.org/10.1016/0003-4916(78)90039-8). URL: <https://doi.org/10.1016/0003-4916(78)90039-8>.

*Commentary.*

On a plaquette crossing the reflection plane, site gauges transform each seam link at its negative and positive endpoints. The four resulting endpoint factors cancel except for conjugation at the starting site.

**Theorem 1.3 (Gauge invariance of the Wilson action).**

Lean statement: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_action_gauge_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_action_gauge_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Konrad Osterwalder and Erhard Seiler (1978). *Gauge Field Theories on a Lattice*. DOI: [10.1016/0003-4916(78)90039-8](https://doi.org/10.1016/0003-4916(78)90039-8). URL: <https://doi.org/10.1016/0003-4916(78)90039-8>.

*Commentary.*

The same cancellation holds on every seam plaquette when each seam link transforms by the site gauges on both halves. Summing gives gauge invariance of the full Wilson action.

**Theorem 1.4 (Time reflection of the Wilson action).**

Lean statement: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_action_reflection_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_action_reflection_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Konrad Osterwalder and Erhard Seiler (1978). *Gauge Field Theories on a Lattice*. DOI: [10.1016/0003-4916(78)90039-8](https://doi.org/10.1016/0003-4916(78)90039-8). URL: <https://doi.org/10.1016/0003-4916(78)90039-8>.

*Commentary.*

Time reflection swaps the two halves and inverts the seam links. The two interior actions are interchanged. Each seam holonomy is conjugate to the inverse of its original value, which preserves its real trace.

**Theorem 1.5 (Osterwalder–Schrader reflection positivity).**

Lean statement: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_reflection_positivity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_reflection_positivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Konrad Osterwalder and Erhard Seiler (1978). *Gauge Field Theories on a Lattice*. DOI: [10.1016/0003-4916(78)90039-8](https://doi.org/10.1016/0003-4916(78)90039-8). URL: <https://doi.org/10.1016/0003-4916(78)90039-8>.

*Commentary.*

For every integrable complex observable of one half and every nonnegative coupling, the Wilson expectation of the reflected conjugate times the observable is a nonnegative real. Use two independent Haar boundary gauges and replace the seam gauge by their relative gauge. The crossing action is then a real dot product of the real and imaginary matrix entries. Each term of its exponential series integrates to a sum of squared moduli with nonnegative coefficients. The uniform bound on the crossing action supplies an integrable majorant. The Haar change of variables applies to gauge-variant as well as gauge-invariant observables.

**Theorem 1.6 (Norm of a physical class).**

Lean statement: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_os_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_os_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Konrad Osterwalder and Erhard Seiler (1978). *Gauge Field Theories on a Lattice*. DOI: [10.1016/0003-4916(78)90039-8](https://doi.org/10.1016/0003-4916(78)90039-8). URL: <https://doi.org/10.1016/0003-4916(78)90039-8>.

*Commentary.*

Split each half configuration into its boundary links and its other links. Integrate the observable over the other links with the remainder of the half action as weight. The boundary kernel induces a pre-inner product on the reduced observables, and quotienting by its null space gives the physical pre-Hilbert space. The class norm is the square root of the unnormalized reflected expectation.

**Theorem 1.7 (Normalized Osterwalder–Schrader seminorm).**

Lean statement: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_os_seminorm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_os_seminorm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Konrad Osterwalder and Erhard Seiler (1978). *Gauge Field Theories on a Lattice*. DOI: [10.1016/0003-4916(78)90039-8](https://doi.org/10.1016/0003-4916(78)90039-8). URL: <https://doi.org/10.1016/0003-4916(78)90039-8>.

*Commentary.*

Divide the physical class norm by the square root of the positive Wilson partition function. This defines a seminorm on integrable half observables, equal to the square root of the real part of the normalized diagonal Gibbs pairing.

**Theorem 1.8 (Mixed Gibbs pairing on the physical quotient).**

Lean statement: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_os_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_os_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Konrad Osterwalder and Erhard Seiler (1978). *Gauge Field Theories on a Lattice*. DOI: [10.1016/0003-4916(78)90039-8](https://doi.org/10.1016/0003-4916(78)90039-8). URL: <https://doi.org/10.1016/0003-4916(78)90039-8>.

*Commentary.*

For two integrable half observables, the inner product of their physical classes equals the mixed Gibbs pairing multiplied by the Wilson partition function. Splitting the action into the boundary step and two half remainders gives the identity by integration over the two interiors.

**Theorem 1.9 (Cauchy–Schwarz for the mixed Gibbs pairing).**

Lean statement: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_os_cauchy_schwarz`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_os_cauchy_schwarz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Konrad Osterwalder and Erhard Seiler (1978). *Gauge Field Theories on a Lattice*. DOI: [10.1016/0003-4916(78)90039-8](https://doi.org/10.1016/0003-4916(78)90039-8). URL: <https://doi.org/10.1016/0003-4916(78)90039-8>.

*Commentary.*

The absolute value of the normalized mixed Gibbs pairing is bounded by the product of the two normalized Osterwalder–Schrader seminorms.

**Theorem 1.10 (Positivity of the one-step transfer operator).**

Lean statement: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_physical_transfer_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_physical_transfer_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Konrad Osterwalder and Erhard Seiler (1978). *Gauge Field Theories on a Lattice*. DOI: [10.1016/0003-4916(78)90039-8](https://doi.org/10.1016/0003-4916(78)90039-8). URL: <https://doi.org/10.1016/0003-4916(78)90039-8>.

*Commentary.*

The integral operator with the Wilson boundary kernel descends to the physical quotient. Its quadratic form on each class is the boundary Haar integral of the squared modulus of the transferred representative, so it is nonnegative.

**Theorem 1.11 (Finite-volume rooted-component bound).**

Lean statement: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_strong_coupling_finite_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_strong_coupling_finite_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Konrad Osterwalder and Erhard Seiler (1978). *Gauge Field Theories on a Lattice*. DOI: [10.1016/0003-4916(78)90039-8](https://doi.org/10.1016/0003-4916(78)90039-8). URL: <https://doi.org/10.1016/0003-4916(78)90039-8>.

*Commentary.*

For a unitary representation of positive dimension with a nontrivial scalar central character, expand each plaquette weight into one plus its activity. Mark a link of the rectangular loop and group plaquettes by the component rooted at that link. Central Haar changes of variables cancel the components that fail to cover a cell under projection onto the rectangle. The norm is bounded by the sum of the surviving activity bounds and also by one.

**Theorem 1.12 (Finite geometric bound).**

Lean statement: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_strong_coupling_geometric_finite_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_strong_coupling_geometric_finite_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Konrad Osterwalder and Erhard Seiler (1978). *Gauge Field Theories on a Lattice*. DOI: [10.1016/0003-4916(78)90039-8](https://doi.org/10.1016/0003-4916(78)90039-8). URL: <https://doi.org/10.1016/0003-4916(78)90039-8>.

*Commentary.*

A component covering all cells has at least R times T plaquettes and at most the total number of plaquettes in the box. Each link is incident to at most six plaquettes and each plaquette has at most twenty neighbors. Counting the rooted components and bounding each activity by exp(beta times d) minus one gives a finite geometric sum with ratio q equal to eighty times that activity bound.

**Theorem 1.13 (Volume-uniform strong-coupling area law).**

Lean statement: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_strong_coupling_area_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_strong_coupling_area_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Konrad Osterwalder and Erhard Seiler (1978). *Gauge Field Theories on a Lattice*. DOI: [10.1016/0003-4916(78)90039-8](https://doi.org/10.1016/0003-4916(78)90039-8). URL: <https://doi.org/10.1016/0003-4916(78)90039-8>.

*Commentary.*

For nonnegative coupling beta, positive rectangle sides R and T, and q less than one, the norm of the normalized rectangular Wilson loop expectation is at most 6 q^(R T) / (80 (1 - q)), where q = 80 (exp(beta d) - 1) and d is the representation dimension. The same estimate applies to every open box containing the rectangle. The nontrivial scalar central character is used in the cancellation.

## References

- Truth anchor: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_action_gauge_invariant`
- Truth anchor: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_action_reflection_invariant`
- Truth anchor: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_os_cauchy_schwarz`
- Truth anchor: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_os_norm`
- Truth anchor: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_os_pairing`
- Truth anchor: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_os_seminorm`
- Truth anchor: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_physical_transfer_nonneg`
- Truth anchor: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_plaquette_gauge_invariant`
- Truth anchor: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_reflection_positivity`
- Truth anchor: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_seam_plaquette_gauge_invariant`
- Truth anchor: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_strong_coupling_area_bound`
- Truth anchor: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_strong_coupling_finite_bound`
- Truth anchor: `D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.wilson_strong_coupling_geometric_finite_bound`
