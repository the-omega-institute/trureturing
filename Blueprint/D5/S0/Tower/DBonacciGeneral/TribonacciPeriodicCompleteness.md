# Tribonacci Periodic Completeness

## Abstract

Ten disjoint cycles exhaust every real Tribonacci periodic state through period five.

**Theorem 1.1 (Orbit states equal all generated fixed points).**

$$\mathit{tribonacciEnumeratedOrbitStatesFive} = \mathit{tribonacciPeriodicPointCodesFive}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicCompleteness.tribonacci_enumerated_orbit_states_eq_fixed_points` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expanding every closed itinerary through period five shows that its fixed-point code occurs on one of the explicit cycles, and conversely.

**Theorem 1.2 (Ten cycles partition thirty-seven phase states).**

$$\operatorname{length}\left(\mathit{tribonacciPeriodicOrbitRepresentativesFive}\right) = 10 \land \operatorname{card}\left(\mathit{tribonacciEnumeratedOrbitStatesFive}\right) = 37$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicCompleteness.tribonacci_periodic_orbit_partition_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Global code distinctness converts the summed primitive periods into exactly thirty-seven different phase states.

**Theorem 1.3 (The real periodic-orbit enumeration is complete).**

$$\forall p \in N, s \in \mathit{TribonacciPeriodicState},\; \left(\left(p \ge 1 \land p \le 5\right) \land \operatorname{iterate}\left(\mathit{tribonacciPeriodicTransition}, p, s\right) = s\right) \Rightarrow s \in \mathit{decodedRepresentativeOrbitUnion}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicCompleteness.tribonacci_periodic_orbit_enumeration_complete_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonzero period at most five, any real state fixed by that iterate lies on one of the ten decoded representative cycles.

## References

- Truth anchor: `D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicCompleteness.tribonacci_enumerated_orbit_states_eq_fixed_points`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicCompleteness.tribonacci_periodic_orbit_enumeration_complete_five`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicCompleteness.tribonacci_periodic_orbit_partition_five`
- Dependency: [D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicEnumeration](TribonacciPeriodicEnumeration.md)
