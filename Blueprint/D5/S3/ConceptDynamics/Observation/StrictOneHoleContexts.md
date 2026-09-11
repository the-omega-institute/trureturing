# Strict One-Hole Contexts

## Abstract

All finite strict one-hole observations determine the greatest strong congruence below the readout kernel.

The state carrier, symbol set and readout codomain are arbitrary. Each symbol has a finite arity, possibly zero, and an Option-valued operation. An arbitrary domain with a function on its subtype gives exactly such a partial operation by the classical Part/Option equivalence. None means outside the domain; some x records the actual output x. Composition uses bind and propagates failure strictly.

A generator chooses a symbol, one of its slots, and exactly one parameter for every other slot. All state values are allowed as parameters. No default state is needed, and a nullary symbol has no generator. Contexts are the range of the denotation of finite generator words as partial functions; the empty word denotes the identity. A successful readout is tagged with some and remains distinct from none even when the readout has a failure-like value.

**Theorem 1.1 (Semantic contexts and finite words).**

Lean statement: `D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts.forall_contexts_iff_words`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts.forall_contexts_iff_words` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of observations for every function in the semantic context family is equivalent to equality for every finite generator word. Different words may denote the same function.

**Theorem 1.2 (The greatest strong domain-preserving congruence).**

Lean statement: `D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts.contextual_equivalence_is_greatest`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts.contextual_equivalence_is_greatest` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Contextual equivalence is a strong congruence, lies in the kernel of the readout, and contains every strong congruence lying in that kernel. Strong congruence means that coordinatewise related tuples belong to the operation domain simultaneously and have related outputs when defined. Replacing coordinates one at a time uses every slot and the actual fixed parameters at that step. For greatestness, Option of the candidate quotient records both failure and the output class; the readout factors through that quotient. No inhabitedness or surjectivity hypothesis is needed.

**Theorem 1.3 (Extending the signature refines equivalence).**

Lean statement: `D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts.signature_extension_refines`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts.signature_extension_refines` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An extension embeds the old symbols, preserves each old arity, and preserves the entire Option-valued operation after arity transport. Thus both its domain and every normal value are unchanged. Contextual equivalence for the extended signature is contained in contextual equivalence for the original signature.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts.contextual_equivalence_is_greatest`
- Truth anchor: `D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts.forall_contexts_iff_words`
- Truth anchor: `D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts.signature_extension_refines`
- Dependency: [D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality](../Interventions/DynamicClosureMinimality.md)
