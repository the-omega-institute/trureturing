# Partial Graph Information Order

## Abstract

Required and forbidden edge information induces a contravariant order on compatible causal models and identified query values.

A partial causal diagram records edges known to be present, edges known to be absent, and leaves every other pair unresolved. A stronger diagram retains all assertions of a weaker diagram and may add more.

Compatibility is antitone in information: every complete graph satisfying the stronger diagram also satisfies the weaker one. The same inclusion transfers directly to compatible structural models and their scalar query values.

The generic nonconvex identification library then transports valid bounds through the refinement. Attained stronger-family endpoints establish the expected monotonic movement of exact lower and upper bounds.

**Theorem 1.1 (Stronger partial diagrams have fewer compatible graphs).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/PartialGraphInformationOrder.compatible_antitone`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/PartialGraphInformationOrder.compatible_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Required-edge and forbidden-edge inclusion are checked separately and then recombined into the weaker compatibility certificate.

**Theorem 1.2 (Stronger graph information removes identified query values).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/PartialGraphInformationOrder.identified_set_antitone`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/PartialGraphInformationOrder.identified_set_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every stronger-family model is reused as a weaker-family witness with the same scalar query value.

**Theorem 1.3 (Partial graph refinement raises attained lower endpoints).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/PartialGraphInformationOrder.lower_endpoint_monotone_under_refinement`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/PartialGraphInformationOrder.lower_endpoint_monotone_under_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A bound valid for the weaker outer family applies to an attaining witness in the stronger inner family. The companion theorem gives the reversed inequality for upper endpoints.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/PartialGraphInformationOrder.compatible_antitone`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/PartialGraphInformationOrder.identified_set_antitone`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/PartialGraphInformationOrder.lower_endpoint_monotone_under_refinement`
- Dependency: [D5/S3/ConceptDynamics/Causal/NonconvexSharpIdentification](../Causal/NonconvexSharpIdentification.md)
