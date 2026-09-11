# Cartesian Domains Do Not Imply Independence

## Abstract

A probability measure on the full Cartesian domain has dependent coordinates.

**Theorem 1.1 (The coordinates are actual random variables).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeWorld/WorldProbabilityBoundary.coordinates_measurable`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeWorld/WorldProbabilityBoundary.coordinates_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The domain is the world subtype of the full Cartesian valuation set, equivalent to the product of the two value types. Both crossed worlds remain in the underlying domain. The value and world measurable spaces contain all subsets. Formula projection is omitted; the resolving Lean declaration is the mathematical statement.

**Theorem 1.2 (A measurable rectangle violates factorization).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeWorld/WorldProbabilityBoundary.rectangle_masses`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeWorld/WorldProbabilityBoundary.rectangle_masses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual Mathlib measure is the sum of two Dirac measures with weight one half each, with its probability property proved. Both marginal values have mass one half. The rectangle where both coordinates equal one has mass one half, while the product of its marginal masses is one quarter. The second diagonal atom is also checked as measure-construction evidence. Formula projection is omitted; the resolving Lean declaration is the mathematical statement.

**Theorem 1.3 (Cartesian domain alone does not imply probabilistic independence).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeWorld/WorldProbabilityBoundary.cartesian_probability_refutation`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeWorld/WorldProbabilityBoundary.cartesian_probability_refutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The refuted closed claim quantifies over every probability measure on this full Cartesian world domain. Its conclusion is the actual Mathlib IndepFun for the coordinate random variables. The proof uses the upstream measurable-rectangle identity, with no invented independence predicate. Formula projection is omitted; the resolving Lean declaration is the mathematical statement.

## References

- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeWorld/WorldProbabilityBoundary.cartesian_probability_refutation`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeWorld/WorldProbabilityBoundary.coordinates_measurable`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeWorld/WorldProbabilityBoundary.rectangle_masses`
- Dependency: [D5/S3/ConceptDynamics/SpacetimeWorld/JointMarginalBoundary](JointMarginalBoundary.md)
