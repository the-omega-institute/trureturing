# Nonconvex Sharp Identification

## Abstract

Nonconvex identified sets separate endpoint exactness, outer-relaxation validity, and complete range sharpness.

Polynomial cross-world restrictions can produce disconnected or otherwise nonconvex feasible families. Universal endpoint bounds and attaining endpoint models remain meaningful, while interval filling requires an additional argument.

A bound established on an outer relaxation transfers to the inner model by feasible-set inclusion. Such a bound may remain loose because the relaxation can contain mixtures that violate the nonlinear restriction.

The two-point example isolates the missing premise. Zero and two are exact attained endpoints, yet one is not feasible. Endpoint attainment alone therefore cannot replace convexity or a direct target-by-target construction.

**Theorem 1.1 (Outer-relaxation lower bounds remain valid for the inner model).**

Lean statement: `D5/S3/ConceptDynamics/Causal/NonconvexSharpIdentification.valid_lower_bound_of_outer_relaxation`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/NonconvexSharpIdentification.valid_lower_bound_of_outer_relaxation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Feasible-set containment is sufficient to transfer universal validity. No convexity, topology, or attainment assumption is used.

**Theorem 1.2 (Outer-relaxation upper bounds remain valid for the inner model).**

Lean statement: `D5/S3/ConceptDynamics/Causal/NonconvexSharpIdentification.valid_upper_bound_of_outer_relaxation`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/NonconvexSharpIdentification.valid_upper_bound_of_outer_relaxation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the upper-bound counterpart used when a semialgebraic model is relaxed to a polyhedral or convex feasible family.

**Theorem 1.3 (A disconnected range can have two exact endpoints).**

Lean statement: `D5/S3/ConceptDynamics/Causal/NonconvexSharpIdentification.twoPointProblem_exact_endpoints`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/NonconvexSharpIdentification.twoPointProblem_exact_endpoints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The feasible query range containing only zero and two has exact lower and upper endpoints.

**Theorem 1.4 (Endpoint attainment without convexity does not prove interval sharpness).**

Lean statement: `D5/S3/ConceptDynamics/Causal/NonconvexSharpIdentification.endpoint_attainment_without_convexity_does_not_fill_interval`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/NonconvexSharpIdentification.endpoint_attainment_without_convexity_does_not_fill_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The target one lies between the two exact endpoints but has no feasible preimage, formally blocking the convex interpolation inference in nonlinear models.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Causal/NonconvexSharpIdentification.endpoint_attainment_without_convexity_does_not_fill_interval`
- Truth anchor: `D5/S3/ConceptDynamics/Causal/NonconvexSharpIdentification.twoPointProblem_exact_endpoints`
- Truth anchor: `D5/S3/ConceptDynamics/Causal/NonconvexSharpIdentification.valid_lower_bound_of_outer_relaxation`
- Truth anchor: `D5/S3/ConceptDynamics/Causal/NonconvexSharpIdentification.valid_upper_bound_of_outer_relaxation`
