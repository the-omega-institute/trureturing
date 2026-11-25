# Validity Preservation by Admissible Transport

## Abstract

Admission-preserving transport pulls target validity back to the source.

**Theorem 1.1 (Validity is preserved by an admission map).**

$$\forall X, Y: Type,\\{}sourceAdmissible: X \to Prop, targetAdmissible: Y \to Prop,\\{}h: X \to Y, P: Y \to Prop,\\{}targetValid: {\forall y: Y, targetAdmissible(y) \Rightarrow P(y)},\\{}admissionPreserving: \forall x: X, sourceAdmissible(x) \Rightarrow targetAdmissible(h(x)),\\{}\forall x: X, sourceAdmissible(x) \Rightarrow P(h(x)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Transport/AdmissionValidityPreservation.validity_preserved_by_admission_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Validity in the target is the source's public quantifier: every target state satisfying the target admission predicate satisfies P.

Admission preservation sends every source state satisfying the source predicate to a target state satisfying the target predicate.

For an admissible source state x, admission preservation supplies target admissibility of h(x), so target validity supplies P(h(x)), exactly the value of the pulled-back predicate at x.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Transport/AdmissionValidityPreservation.validity_preserved_by_admission_map`
