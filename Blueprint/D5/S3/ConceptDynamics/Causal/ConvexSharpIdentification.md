# Convex Sharp Identification

## Abstract

Convex feasible model families and affine queries turn attained valid endpoints into exact identified intervals.

The logical core of scalar partial identification is independent of any particular causal graph or linear program. A feasible family, a scalar query, a convex blending operation, and affine query behavior are sufficient to state sharpness abstractly.

Universal certificates and primal witnesses play different roles. A universal lower or upper bound proves validity. A feasible model attaining the same endpoint proves optimality. Convexity then fills every interior query value between two attained endpoints.

Feasible-set refinement formalizes additional information. If every model satisfying stronger assumptions also satisfies weaker assumptions and the query is unchanged, valid bounds survive refinement. Exact lower endpoints can only move upward and exact upper endpoints can only move downward.

**Theorem 1.1 (Attained endpoints and convexity imply interval sharpness).**

Lean statement: `D5/S3/ConceptDynamics/Causal/ConvexSharpIdentification.sharp_interval_of_valid_bounds_and_endpoint_witnesses`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/ConvexSharpIdentification.sharp_interval_of_valid_bounds_and_endpoint_witnesses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given valid lower and upper bounds, feasible models attaining both endpoints, closure under convex blends, and affine query behavior, a target is attainable exactly when it lies between the two endpoints.

**Theorem 1.2 (Stronger assumptions raise exact lower endpoints).**

Lean statement: `D5/S3/ConceptDynamics/Causal/ConvexSharpIdentification.exact_lower_endpoint_monotone_under_refinement`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/ConvexSharpIdentification.exact_lower_endpoint_monotone_under_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A lower bound valid for a weaker feasible family applies to every stronger feasible model. An attaining stronger-family witness therefore cannot lie below the weaker exact lower endpoint.

**Theorem 1.3 (Stronger assumptions lower exact upper endpoints).**

Lean statement: `D5/S3/ConceptDynamics/Causal/ConvexSharpIdentification.exact_upper_endpoint_monotone_under_refinement`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/ConvexSharpIdentification.exact_upper_endpoint_monotone_under_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The dual information-order statement holds at the upper endpoint: an attaining stronger-family witness cannot exceed a valid weaker-family upper bound.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Causal/ConvexSharpIdentification.exact_lower_endpoint_monotone_under_refinement`
- Truth anchor: `D5/S3/ConceptDynamics/Causal/ConvexSharpIdentification.exact_upper_endpoint_monotone_under_refinement`
- Truth anchor: `D5/S3/ConceptDynamics/Causal/ConvexSharpIdentification.sharp_interval_of_valid_bounds_and_endpoint_witnesses`
