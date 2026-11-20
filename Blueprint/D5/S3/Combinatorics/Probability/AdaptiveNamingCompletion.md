# Completing a naming after adaptive replies

## Abstract

Deferred completion of a finite partial naming preserves the joint law at a protocol's stopping point.

**Theorem 1.1 (Joint law of the stopped transcript and completed naming state).**

Lean statement: `D5/S3/Combinatorics/Probability/AdaptiveNamingCompletion.adaptive_name_completion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Probability/AdaptiveNamingCompletion.adaptive_name_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The initial partial state contains a finite set of already named vertices, an injective naming on those vertices and a disjoint set of available names. At least one full injection completes the partial naming using those available names.

A finite deterministic protocol either stops or selects its next query from the previous replies. Each query's ordered vertex request may depend on the current partial naming. In the deferred experiment, the reply is drawn from the current reply law. The update preserves the old names, assigns the reply at each requested vertex, and removes exactly the names used by the expanded assignment from the available set. The expanded domain is the union of the old and requested vertices. At a stop the remaining names are completed uniformly. In the other experiment, a uniform completion is drawn initially and held fixed. The same query reads its reply from that injection and uses the same update to the partial state.

The two experiments give the same joint law of the ordered transcript, terminal partial naming state and full injection. At a query, the joint law of reply and completion lets the completion move before the query. Conditional on the reply, the protocol has a specified successor, to which the inductive equality applies. At a stop both experiments retain the same partial state and completion.

## References

- Truth anchor: `D5/S3/Combinatorics/Probability/AdaptiveNamingCompletion.adaptive_name_completion`
- Dependency: [D5/S3/Combinatorics/Probability/JointNamingReplyCompletion](JointNamingReplyCompletion.md)
- Dependency: [D5/S3/ConceptDynamics/Experiment/PassiveAdaptiveTranscriptUpperBound](../../ConceptDynamics/Experiment/PassiveAdaptiveTranscriptUpperBound.md)
