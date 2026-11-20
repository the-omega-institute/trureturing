# Exact positive expansivity on finite multigraph realizations

## Abstract

Exact positive expansivity on finite multigraph realizations

**Theorem 1.1 (Exact positive expansivity on the original graph).**

Lean statement: `D5/S1/Dynamics/Shadowing/FiniteMultigraphExactDynamics.exists_exact_positivelyExpansive`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/FiniteMultigraphExactDynamics.exists_exact_positivelyExpansive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three-segment subdivision preserves connectivity and the incidence count condition. Its affine edge-walk map transports through the proved homeomorphism to any metric realization of the original graph, with loops and parallel edges allowed.

**Theorem 1.2 (The degree-one obstruction gives a complete classification).**

Lean statement: `D5/S1/Dynamics/Shadowing/FiniteMultigraphExactDynamics.exists_exact_finitelyPositiveExpansive_iff`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/FiniteMultigraphExactDynamics.exists_exact_finitelyPositiveExpansive_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite connected graph with at least one edge admits a continuous topologically exact map with a finite forward Bowen bound if and only if no vertex has exactly one incident flag. The constructive direction gives positive expansivity. For the converse the subdivision homeomorphism transports a pendant arc back to the original graph, where it obstructs every finite Bowen bound.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/FiniteMultigraphExactDynamics.exists_exact_finitelyPositiveExpansive_iff`
- Truth anchor: `D5/S1/Dynamics/Shadowing/FiniteMultigraphExactDynamics.exists_exact_positivelyExpansive`
- Dependency: [D5/S1/Dynamics/Shadowing/ExactExpansiveConjugacy](ExactExpansiveConjugacy.md)
- Dependency: [D5/S1/Dynamics/Shadowing/FiniteGraphExactDynamics](FiniteGraphExactDynamics.md)
- Dependency: [D5/S1/Dynamics/Shadowing/TripleEdgeSubdivisionRealization](TripleEdgeSubdivisionRealization.md)
