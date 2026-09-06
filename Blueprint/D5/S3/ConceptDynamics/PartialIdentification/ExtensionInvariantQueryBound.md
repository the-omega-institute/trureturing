# Extension-Invariant Causal Query Bounds

## Abstract

Equivariant relabelings of finite response-signature programs preserve feasibility, event values, and the complete identified set.

Two compatible total orders can use different response-signature carriers. Order invariance requires a carrier equivalence that preserves every observational constraint row, its right-hand side, and the Boolean counterfactual query evaluation.

Mass is transported by composing with the inverse signature equivalence. Finite-sum reindexing proves preservation of event objectives and every constraint value.

The resulting theorem identifies the exact proof payload needed to justify total-order invariance. Merely knowing that both orders extend the same partial order does not discharge row and query equivariance.

**Theorem 1.1 (Query event mass is invariant under preserving signature relabeling).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/ExtensionInvariantQueryBound.signatureEventMass_relabel`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/ExtensionInvariantQueryBound.signatureEventMass_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An equivalence reindexes the finite signature sum, while preservation of the Boolean event makes each transported term equal.

**Theorem 1.2 (Equivariant response-signature relabeling preserves feasibility).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/ExtensionInvariantQueryBound.feasible_relabel_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/ExtensionInvariantQueryBound.feasible_relabel_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every compiled constraint row has the same finite sum after relabeling, and the right-hand sides agree.

**Theorem 1.3 (Preserving signature equivalences give identical identified sets).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/ExtensionInvariantQueryBound.identified_set_invariant_under_signature_equivalence`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/ExtensionInvariantQueryBound.identified_set_invariant_under_signature_equivalence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Forward and inverse mass transports map every feasible witness at a target value to a feasible witness for the other order at the same value.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/ExtensionInvariantQueryBound.feasible_relabel_iff`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/ExtensionInvariantQueryBound.identified_set_invariant_under_signature_equivalence`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/ExtensionInvariantQueryBound.signatureEventMass_relabel`
- Dependency: [D5/S3/ConceptDynamics/PartialIdentification/CausalOrderLinearProgram](CausalOrderLinearProgram.md)
