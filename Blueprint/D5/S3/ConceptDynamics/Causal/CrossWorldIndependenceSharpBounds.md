# Cross-World Independence Sharp Bounds

## Abstract

A polynomial cross-world independence restriction collapses a Boolean joint query to a sharp singleton and exposes a genuine nonconvex boundary.

For a normalized two-by-two event coupling, independence is encoded by vanishing of the determinant. This is a polynomial equality in the four cell masses.

Combining the determinant equation with normalization and the two marginal rows forces the true-true joint mass to equal the product of the marginals. The explicit product coupling proves attainment, so the identified range is a singleton.

The unrestricted family of independent couplings is not closed under mixtures. Two degenerate independent laws have a normalized midpoint with nonzero determinant. This formally marks the point at which convex interpolation cannot be used without checking the actual feasible family.

**Theorem 1.1 (The determinant restriction identifies the joint mass as the marginal product).**

Lean statement: `D5/S3/ConceptDynamics/Causal/CrossWorldIndependenceSharpBounds.independent_joint_event_eq_product`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/CrossWorldIndependenceSharpBounds.independent_joint_event_eq_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof eliminates the other three cells using the linear marginal equations and then verifies the remaining polynomial identity exactly.

**Theorem 1.2 (The cross-world joint query has an exact singleton identified set).**

Lean statement: `D5/S3/ConceptDynamics/Causal/CrossWorldIndependenceSharpBounds.independent_joint_event_sharp_singleton_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/CrossWorldIndependenceSharpBounds.independent_joint_event_sharp_singleton_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Necessity follows from polynomial elimination. Sufficiency is witnessed by the explicit product coupling for probability-valued marginals.

**Theorem 1.3 (Independent event couplings are globally nonconvex).**

Lean statement: `D5/S3/ConceptDynamics/Causal/CrossWorldIndependenceSharpBounds.independent_event_couplings_not_closed_under_midpoint`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/CrossWorldIndependenceSharpBounds.independent_event_couplings_not_closed_under_midpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two normalized independent endpoint laws are constructed. Their normalized midpoint violates the determinant equation, providing a replayable obstruction to unqualified convex mixing.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Causal/CrossWorldIndependenceSharpBounds.independent_event_couplings_not_closed_under_midpoint`
- Truth anchor: `D5/S3/ConceptDynamics/Causal/CrossWorldIndependenceSharpBounds.independent_joint_event_eq_product`
- Truth anchor: `D5/S3/ConceptDynamics/Causal/CrossWorldIndependenceSharpBounds.independent_joint_event_sharp_singleton_iff`
- Dependency: [D5/S3/ConceptDynamics/Causal/FiniteEventCouplingSharpBounds](FiniteEventCouplingSharpBounds.md)
- Dependency: [D5/S3/ConceptDynamics/Causal/NonconvexSharpIdentification](NonconvexSharpIdentification.md)
