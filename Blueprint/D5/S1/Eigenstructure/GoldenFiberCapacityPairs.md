# Golden Fiber Capacity Pairs

## Abstract

The golden fiber capacities are the adjacent integer pairs four-five and two-three.

**Theorem 1.1 (The golden fiber capacities are exact adjacent pairs).**

$$\{\lfloor\varphi^{3}\rfloor, \operatorname{ceil}(\varphi^{3})\} = \{4, 5\} \land \{\lfloor\varphi^{2}\rfloor, \operatorname{ceil}(\varphi^{2})\} = \{2, 3\}$$

*Proof.* Machine-checked in Lean as `D5/S1/Eigenstructure/GoldenFiberCapacityPairs.golden_fiber_capacity_pairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The declaration packages the four frozen floor and ceiling values into the two finite-set equalities stated by the source. It directly reuses golden_power_floor_ceil_pairs and does not reprove any rounding fact.

Pinned Mathlib was searched for floor and ceiling APIs, golden-ratio identities, and an exact finite-set pair theorem. Generic APIs and the identities were present, but no declaration states these assembled pairs.

This deposit closes only the explicit capacity-pair equalities in source proposition 6.42, clause 2. The support interval, Sturmian distribution, and asymptotic frequency assertions remain outside this declaration.

## References

- Truth anchor: `D5/S1/Eigenstructure/GoldenFiberCapacityPairs.golden_fiber_capacity_pairs`
