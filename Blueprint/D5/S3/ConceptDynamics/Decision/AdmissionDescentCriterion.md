# Admission Descent Criterion

## Abstract

Admission descends through a visible quotient exactly when its fibers have no mixed boundary and its universal core and existential hull coincide.

**Theorem 1.1 (Fiber constancy is simultaneous core and hull equality).**

$$\operatorname{FiberConstant}\left(q, A\right) \Leftrightarrow (A = \operatorname{universalFiberCore}\left(q, A\right) \land A = \operatorname{existentialFiberHull}\left(q, A\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Decision/AdmissionDescentCriterion.fiberConstant_iff_core_eq_and_hull_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If admission is constant on visible fibers, the current state witnesses existential hull membership and transports membership to every state in the universal core. Conversely, universal-core equality alone transports admission membership in both directions across a fiber.

**Theorem 1.2 (Four equivalent clauses characterize admission descent).**

$$(\exists Abar: B \to \operatorname{Prop}, \forall x, x \in A \Leftrightarrow Abar(q(x))) \Leftrightarrow \operatorname{FiberConstant}\left(q, A\right) \Leftrightarrow \operatorname{admissionBoundary}\left(q, A\right) = \emptyset \Leftrightarrow (A = \operatorname{universalFiberCore}\left(q, A\right) \land A = \operatorname{existentialFiberHull}\left(q, A\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Decision/AdmissionDescentCriterion.admission_descent_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an anchored state space, an admission predicate factors through the visible quotient exactly when it is constant on each quotient fiber.

The same condition is equivalent both to emptiness of the mixed-fiber boundary and to simultaneous equality with the universal fiber core and existential fiber hull.

The factorization and empty-boundary clauses reuse the frozen repository theorem AnswerabilityCriterion.answerability_criterion. The new proof obligation is the simultaneous core-hull characterization.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Decision/AdmissionDescentCriterion.admission_descent_criterion`
- Truth anchor: `D5/S3/ConceptDynamics/Decision/AdmissionDescentCriterion.fiberConstant_iff_core_eq_and_hull_eq`
- Dependency: [D5/S0/Rewriting/Quotients/AnswerabilityCriterion](../../../S0/Rewriting/Quotients/AnswerabilityCriterion.md)
