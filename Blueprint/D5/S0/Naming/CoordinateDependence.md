# Coordinate Dependence

## Abstract

Dependent coordinates are witnessed by separating pairs with distinct invariant values.

**Definition 1.1 (Dependency set).**

$$\operatorname{dependencySet}(\operatorname{separatesAt}, \operatorname{invariant}) = \{coordinate \mid \exists left, right, \operatorname{separatesAt}(coordinate, left, right) \land \operatorname{invariant}(left) \neq \operatorname{invariant}(right)\}$$

*Formalization.* `D5/S0/Naming/CoordinateDependence.dependencySet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary coordinate, system, and value types, separatesAt records the primitive assertion that two systems form a separating pair at a coordinate. The dependency set contains exactly those coordinates for which such a pair has unequal invariant values.

Pinned Mathlib's Function.DependsOn describes factorization through selected product coordinates and is not this separating-pair definition. Repository and pinned-library searches found no matching set-valued declaration, so this definition introduces only the generic abstraction stated here.

The Lean module checks both directions of non-hollowness with concrete examples: one relation and invariant make coordinate zero a member, while a constant invariant has the empty dependency set even when every pair separates.

## References

- Truth anchor: `D5/S0/Naming/CoordinateDependence.dependencySet`
