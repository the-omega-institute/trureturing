# Authorization and Factual Correctness

## Abstract

Authorization provenance can pass while a result target fails.

**Theorem 1.1 (Authorization does not imply factual correctness).**

$$\forall I, A, R: \operatorname{Type}, i: I, a: A, r_{ok}, r_{bad}: R, r_{bad} \neq r_{ok} \Rightarrow\ \exists authorize: I \to A \to \operatorname{Prop}, \exists target, actual: I \to R,\ \operatorname{authorizationAudit}(authorize, \operatorname{const}(a)) \land \neg \operatorname{resultAudit}(target, actual).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/LegitimacyCorrectness.authorized_process_can_fail_factually` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source separates two audits: authorization provenance checks the executed action against an authorization rule, while a result audit compares the actual result with its target.

For every inhabited input, action, and pair of distinct results, the source primitives construct an authorized constant execution whose result audit fails. The authorization and result predicates are not defined from that failure.

Repository searches found no exact separation theorem; the proof is the direct constant countermodel over the source carriers.

## References

- Truth anchor: `D5/S3/ConceptDynamics/LegitimacyCorrectness.authorized_process_can_fail_factually`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](ConceptFiberDecomposition.md)
