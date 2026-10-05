# Response kernel successor

## Abstract

The response relation of numbered incoming lifts has an exact successor recursion.

**Theorem 1.1 (Incoming edge lifts determine the successor response).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseKernelRecursion.response_successor_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResponseKernelRecursion.response_successor_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An incoming lift assigns each numbered base edge a map from its terminal state fiber to its initial state fiber. Its depth response records the projected state and the initial lifted state for every path of that length. Two states have the same successor response exactly when their projections agree and their lifts along every numbered incoming edge have the same preceding response.

The forward implication follows by appending an incoming edge to each preceding path. For the converse, every path of positive length decomposes into a prefix and its last numbered edge. Equality of the preceding responses supplies equality after lifting the prefix, and the composition law for path lifts recovers equality along the whole path. Empty prefixes, parallel edge identities and arbitrary state sets are included.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseKernelRecursion.response_successor_iff`
- Dependency: [D5/S3/ConceptDynamics/Coding/CompatibleResponseForgetting](CompatibleResponseForgetting.md)
