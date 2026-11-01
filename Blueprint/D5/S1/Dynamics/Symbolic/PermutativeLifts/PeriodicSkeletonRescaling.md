# Actual periodic-skeleton density under rescaling

## Abstract

Actual periodic-skeleton density under rescaling.

**Theorem 1.1 (Compatible rescaling preserves actual density).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonRescaling.density_eq_of_dvd_of_periodic_coordinates_eq`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonRescaling.density_eq_of_dvd_of_periodic_coordinates_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q and h be positive natural periods of a binary two-sided point, with q dividing h. If the actual q-periodic-coordinate condition agrees with the actual h-periodic-coordinate condition at every signed site, their normalized periodic-skeleton densities are equal. The proof splits a complete h-interval into equally many q-intervals by finProdFinEquiv and counts the same actual periodic coordinates. It retains the universal quantifier over signed integer multiples, and neither assumes nor asserts essentiality of either period. Public escape registrations remain unfinished under https://github.com/the-omega-institute/trureturing/issues/24726; compiled density rescaling is not declared_validated registration evidence.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonRescaling.density_eq_of_dvd_of_periodic_coordinates_eq`
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonDensity](PeriodicSkeletonDensity.md)
