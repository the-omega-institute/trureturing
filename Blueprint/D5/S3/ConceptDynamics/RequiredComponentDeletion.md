# Required Component Deletion

## Abstract

Deleting a presentation component preserves a theorem's eligibility exactly when that component is not among the theorem's requirements.

**Theorem 1.1 (Exact eligibility criterion after deletion).**

$$\operatorname{Eligible}(present \setminus \{c\}, t)\quad \iff\quad \operatorname{Eligible}(present, t)\quad \land\quad \neg requires(t, c)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RequiredComponentDeletion.required_component_deletion_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Eligibility means that every component required by a theorem occurs in the presented component set. After removing c, this condition is equivalent to prior eligibility together with the absence of a requirement edge from the theorem to c.

Both directions are retained. Thus the result proves loss of statement eligibility for a listed load-bearing component and also proves that deleting a genuinely unused component is harmless.

Repository and pinned-Mathlib searches found set and dependency analogues but no theorem with this exact quantified deletion criterion.

**Theorem 1.2 (A required deletion really destroys eligibility).**

$$\exists requires, present, t, c,\quad \operatorname{Eligible}(present, t)\quad \land\quad requires(t, c)\quad \land\quad \neg\operatorname{Eligible}(present \setminus \{c\}, t)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RequiredComponentDeletion.required_component_deletion_can_be_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Boolean presentation supplies a constructive countermodel to any claim that deletion is always harmless: true is required, all components are initially present, and deleting true makes eligibility fail.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RequiredComponentDeletion.required_component_deletion_can_be_strict`
- Truth anchor: `D5/S3/ConceptDynamics/RequiredComponentDeletion.required_component_deletion_iff`
