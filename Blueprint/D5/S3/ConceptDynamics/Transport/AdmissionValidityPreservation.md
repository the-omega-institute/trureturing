# Validity Preservation by Admissible Transport

## Abstract

Admission-preserving transport pulls target validity back to the source.

**Theorem 1.1 (Validity is preserved by an admission map).**

$$\forall X, Y: Type,\\{}sourceAdmissible: X \to Prop, targetAdmissible: Y \to Prop,\\{}h: \operatorname{Concept}\left(X, Y\right), P: Y \to Prop,\\{}targetValid: {\forall y: Y, targetAdmissible(y) \Rightarrow P(y)},\\{}admissionPreserving: \operatorname{MapsTo}\left(h, \{x: X \mid sourceAdmissible(x)\}, \{y: Y \mid targetAdmissible(y)\}\right),\\{}\forall x: X, sourceAdmissible(x) \Rightarrow (P \circ h)(x).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Transport/AdmissionValidityPreservation.validity_preserved_by_admission_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Validity in the target is the source's public quantifier: every target state satisfying the target admission predicate satisfies P.

Admission preservation is the standard MapsTo condition on the source and target admission predicates. Both predicates and the transport map are independent inputs.

For an admissible source state x, admission preservation supplies target admissibility of h(x), so target validity supplies P(h(x)), exactly the value of the pulled-back predicate at x.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Transport/AdmissionValidityPreservation.validity_preserved_by_admission_map`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../ConceptFiberDecomposition.md)
