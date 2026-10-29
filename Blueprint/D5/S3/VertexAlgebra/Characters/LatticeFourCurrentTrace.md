# Finite Four-Current Trace

## Scope

This source records the original finite four-current cycle and its explicit bounded labeled partial-matching coefficient. The cycle uses the actual current blocks on the complete charge and oscillator energy grades. The coefficient keeps the ten partial matchings, the two arc choices on every edge, repeated-frequency edge slots, signed Gram entries, charge weights, and the guarded grade equalities finite.

## Definitions

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeFourCurrentTrace.PM4`

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeFourCurrentTrace.PM4.edges`

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeFourCurrentTrace.actualFourCurrentCycleTrace`

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeFourCurrentTrace.boundedFourCurrentCoefficient`

The trace is the finite `LinearMap.trace` of the right-to-left composition of the four literal original `actualCurrentBlock` maps on the initial grade. The coefficient is an explicit finite sum over the positive charge cutoff, the ten labeled matchings, bounded frequency and winding assignments, the two arc/complement choices, and the residual oscillator grade. No inverse Gram matrix, factorial division, or analytic convergence premise occurs in these definitions.

The full signed-mode recurrence and its transport from the coefficient to the original trace remain a separate proof obligation. The source currently contains the compiled equal-grade zero-mode basis calculation as an internal bridge; it does not establish the all-grade four-current identity.

## References

- Dependency: [D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentTrace](LatticeTwoCurrentTrace.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualConformalState](../LatticeActualConformalState.md)
