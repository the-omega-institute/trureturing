# Covariate Sharp Aggregation

## Abstract

Independently combinable covariate-stratum sharp intervals aggregate to an exact nonnegative weighted sharp interval.

Each covariate stratum supplies an exact scalar identified interval. Global attainability means that one attainable value may be selected in every stratum and combined with fixed nonnegative weights.

Pointwise lower and upper bounds survive weighted summation. A common interpolation parameter simultaneously moves every stratum between its two endpoints and therefore realizes every global value between the weighted endpoints.

The joint-selection premise is substantive. Shared structural parameters, transport restrictions, or other cross-stratum constraints require a different feasible family and are outside this theorem.

**Theorem 1.1 (Nonnegative weights preserve pointwise stratum bounds).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/CovariateSharpAggregation.weightedValue_mono`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/CovariateSharpAggregation.weightedValue_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite summation of the pointwise inequalities gives the global lower or upper bound.

**Theorem 1.2 (The weighted covariate interval is exactly sharp).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/CovariateSharpAggregation.covariate_weighted_sharp_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/CovariateSharpAggregation.covariate_weighted_sharp_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A target lies between the weighted endpoints exactly when jointly attainable stratum values aggregate to that target. Equal endpoints use a boundary witness. Distinct endpoints use one common affine interpolation parameter.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/CovariateSharpAggregation.covariate_weighted_sharp_iff`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/CovariateSharpAggregation.weightedValue_mono`
