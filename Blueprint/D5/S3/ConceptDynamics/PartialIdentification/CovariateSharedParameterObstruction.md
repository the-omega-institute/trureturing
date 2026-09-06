# Covariate Shared-Parameter Obstruction

## Abstract

Sharp covariate-stratum projections need not aggregate sharply when the strata share an unidentified structural parameter.

Two covariate strata respond in complementary ways to one common parameter. If each stratum may choose its parameter independently, each projected identified set is the full interval from zero to one.

The actual joint model requires one parameter for both strata. With equal covariate weights, the two responses cancel and the global query is always one half.

The value one half is forced by the affine complement involution x maps to one minus x and equal weighting. This algebraic fixed-point mechanism makes no claim about the Riemann zeta function or the location of its zeros.

This construction proves that stratum-level sharpness alone is insufficient for weighted global sharpness. Joint combinability, or an equivalent product-feasibility condition, is a substantive causal assumption.

**Theorem 1.1 (Each stratum projection is the exact unit interval).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/CovariateSharedParameterObstruction.local_attainable_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/CovariateSharedParameterObstruction.local_attainable_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either complementary response, every value between zero and one is realized by an admissible stratum-specific parameter, and no value outside the interval is realized.

**Theorem 1.2 (The affine complement involution has fixed point one half).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/CovariateSharedParameterObstruction.complement_fixed_point_eq_half`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/CovariateSharedParameterObstruction.complement_fixed_point_eq_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Solving x equals one minus x gives the unique affine midpoint. The theorem is intentionally independent of analytic number theory.

**Theorem 1.3 (The shared-parameter global range is a singleton).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/CovariateSharedParameterObstruction.shared_parameter_attainable_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/CovariateSharedParameterObstruction.shared_parameter_attainable_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equal weighting of the complementary responses eliminates the common parameter and fixes the global query at one half.

**Theorem 1.4 (Independent weighted sharpness can fail under cross-stratum coupling).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/CovariateSharedParameterObstruction.shared_parameter_invalidates_naive_weighted_sharpness`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/CovariateSharedParameterObstruction.shared_parameter_invalidates_naive_weighted_sharpness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The independent product family realizes global value zero, while the shared-parameter family cannot. This separates projected stratum information from jointly compatible causal models.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/CovariateSharedParameterObstruction.complement_fixed_point_eq_half`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/CovariateSharedParameterObstruction.local_attainable_iff`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/CovariateSharedParameterObstruction.shared_parameter_attainable_iff`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/CovariateSharedParameterObstruction.shared_parameter_invalidates_naive_weighted_sharpness`
- Dependency: [D5/S3/ConceptDynamics/PartialIdentification/CovariateSharpAggregation](CovariateSharpAggregation.md)
