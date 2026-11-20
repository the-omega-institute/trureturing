# Classification of exact finite positive expansivity on simple graphs

## Abstract

Classification of exact finite positive expansivity on simple graphs

**Theorem 1.1 (A piecewise affine exact positively expansive map).**

Lean statement: `D5/S1/Dynamics/Shadowing/FiniteGraphExactDynamics.exists_exact_edgeWalkMap`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/FiniteGraphExactDynamics.exists_exact_edgeWalkMap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each source edge traverses its reduced all-edge walk at constant speed and fixes its endpoints. The closed-cell maps agree on overlaps. Contracting inverse branches prove exactness, and distinct image germs at cell boundaries give uniform expansion.

**Theorem 1.2 (Degree one characterizes the obstruction).**

Lean statement: `D5/S1/Dynamics/Shadowing/FiniteGraphExactDynamics.exists_exact_finitelyPositiveExpansive_iff`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/FiniteGraphExactDynamics.exists_exact_finitelyPositiveExpansive_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nontrivial finite connected simple graph admits a continuous topologically exact finitely positively expansive map precisely when no vertex has degree one. A degree-one vertex gives a pendant arc and rules out every finite Bowen bound.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/FiniteGraphExactDynamics.exists_exact_edgeWalkMap`
- Truth anchor: `D5/S1/Dynamics/Shadowing/FiniteGraphExactDynamics.exists_exact_finitelyPositiveExpansive_iff`
- Dependency: [D5/S1/Dynamics/Shadowing/EdgeSubdivisionDynamics](EdgeSubdivisionDynamics.md)
- Dependency: [D5/S1/Dynamics/Shadowing/FiniteGraphAffineRealization](FiniteGraphAffineRealization.md)
- Dependency: [D5/S3/Combinatorics/Graph/LeaflessDynamics/LeaflessDartTour](../../../S3/Combinatorics/Graph/LeaflessDynamics/LeaflessDartTour.md)
