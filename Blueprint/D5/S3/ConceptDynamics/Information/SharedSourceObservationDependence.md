# Shared Source Observation Dependence

## Abstract

Two copies of one fair Boolean source agree surely but are not independent.

**Theorem 1.1 (Shared fair-source observations are not independent).**

$$\begin{gathered}P(X_{p} = X_{q}) = 1 \land\\{}P(X_{p} = 1) P(X_{q} = 1) = \frac{1}{4} \land\\{}P(X_{p} = 1) P(X_{q} = 1) \neq P(X_{p} = 1 \land X_{q} = 1) \land\\{}P(X_{p} = 1 \land X_{q} = 1) = \frac{1}{2}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Information/SharedSourceObservationDependence.shared_source_observations_are_not_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source law assigns mass one half to each Boolean state. Both observation channels copy that same source state.

Their equality event therefore has probability one. Each one-event has probability one half, so the marginal product is one quarter.

The joint one-event is the single true source state and has probability one half. Its mismatch with the marginal product is the explicit failure of independence.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Information/SharedSourceObservationDependence.shared_source_observations_are_not_independent`
- Dependency: [D5/S3/ConceptDynamics/Information/RefinementEntropyMonotonicity](RefinementEntropyMonotonicity.md)
