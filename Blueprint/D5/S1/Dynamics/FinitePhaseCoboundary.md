# Continuous coboundaries from finite phase towers

## Abstract

Identity return transport on a finite cyclic phase tower gives a continuous transfer.

Let a continuous integer action admit a continuous cyclic phase of positive height h. A continuous group-valued cocycle whose ordered h-step product is one at every phase-zero point has a continuous transfer b with b(Tx) = c(x)b(x), normalized to one on the zero phase. At a point of phase r, move back r steps to the tower base and multiply the intervening cocycle values on the left. Local constancy of the phase proves continuity; identity return transport handles the tower wrap. The target may be a noncommutative topological group. Compactness, minimality and finite target groups are unnecessary.

The ordered product reuses SkewGroupHolonomy in the opposite group. This is a general return-to-coboundary bridge, rather than a claim that a particular symbolic system has identity returns. Such an application must separately supply its actual phase map, continuity, equivariance and return identity. No literature-priority claim is made.

**Definition 1.1 (Left ordered transport).**

Lean statement: `D5/S1/Dynamics/FinitePhaseCoboundary.leftHolonomy`

*Formalization.* `D5/S1/Dynamics/FinitePhaseCoboundary.leftHolonomy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product P starts at one and obeys P(n+1,x) = c(T^n x) P(n,x). Reversing multiplication through the opposite group preserves the order for noncommutative targets.

**Theorem 1.2 (Identity return gives a continuous transfer).**

Lean statement: `D5/S1/Dynamics/FinitePhaseCoboundary.exists_continuous_transfer_of_phase_return`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/FinitePhaseCoboundary.exists_continuous_transfer_of_phase_return` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive cyclic phase height and continuous equivariant phase, identity full return transport on the zero phase yields a continuous normalized solution of b(Tx) = c(x)b(x).

## References

- Truth anchor: `D5/S1/Dynamics/FinitePhaseCoboundary.exists_continuous_transfer_of_phase_return`
- Truth anchor: `D5/S1/Dynamics/FinitePhaseCoboundary.leftHolonomy`
- Dependency: [D5/S1/Dynamics/PeriodicOrbits/SkewGroupHolonomy](PeriodicOrbits/SkewGroupHolonomy.md)
