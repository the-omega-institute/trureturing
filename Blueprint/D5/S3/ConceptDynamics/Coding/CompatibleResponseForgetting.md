# Compatible response forgetting

## Abstract

A compatible numbered path certificate constructs an essential finite square graph with both boundaries forgetting after its lag.

**Theorem 1.1 (Incoming lifts respect response depth).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CompatibleResponseForgetting.incoming_response_step`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CompatibleResponseForgetting.incoming_response_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two states with the same numbered path responses at depth d plus one, lifting the same incoming base edge places their predecessor states in one depth-d response class. Appending that edge to each depth-d path identifies the resulting lifted paths with the original depth-(d+1) observations.

Numbered compatible squares give incoming and outgoing lifts on the R-edge states. Their finite sweeps identify responses with the certificate path bijections, and counting edge fibers yields the first row and column response matrices.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/CompatibleResponseForgetting.incoming_response_step`
- Dependency: [D5/S3/ConceptDynamics/Coding/FirstResponseDiamond](FirstResponseDiamond.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/ResponseQuotientKernel](ResponseQuotientKernel.md)
