# Partial-Graph Completion Ranges

## Abstract

Partial-graph uncertainty yields a union of completion-specific sharp ranges. Its envelope endpoints can be exact even when the full range is disconnected.

Each compatible complete graph carries its own sharp scalar interval. Under epistemic graph uncertainty, a value is attainable when at least one completion admits it.

The resulting identified range is the union of completion-specific intervals. The smallest lower endpoint and largest upper endpoint remain exact when attained by completions.

The union need not fill the envelope interval. Treating unknown graph structure as a probabilistic mixture over graph indices is an additional model assumption that can add query values.

**Theorem 1.1 (The partial-graph identified range is the completion union).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/PartialGraphCompletionRange.partial_graph_range_is_completion_union`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/PartialGraphCompletionRange.partial_graph_range_is_completion_union` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem identifies global attainability exactly with membership in one compatible completion's sharp interval.

**Theorem 1.2 (An attained completion envelope gives an exact global endpoint).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/PartialGraphCompletionRange.exact_lower_endpoint_of_completion_envelope`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/PartialGraphCompletionRange.exact_lower_endpoint_of_completion_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A lower value below every completion-specific lower endpoint is globally valid, and one completion attaining it proves exactness. The module also proves the dual upper statement.

**Theorem 1.3 (Exact envelope endpoints do not force interval sharpness).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/PartialGraphCompletionRange.partial_graph_envelope_need_not_be_sharp_interval`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/PartialGraphCompletionRange.partial_graph_envelope_need_not_be_sharp_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two graph completions with singleton ranges zero and two have exact envelope endpoints, while the intermediate value one remains unattainable.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/PartialGraphCompletionRange.exact_lower_endpoint_of_completion_envelope`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/PartialGraphCompletionRange.partial_graph_envelope_need_not_be_sharp_interval`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/PartialGraphCompletionRange.partial_graph_range_is_completion_union`
- Dependency: [D5/S3/ConceptDynamics/Causal/NonconvexSharpIdentification](../Causal/NonconvexSharpIdentification.md)
