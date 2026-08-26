# Partial Tests Leave a Defect

## Abstract

Partial tests can pass while a disjoint nonempty defect set remains.

**Theorem 1.1 (Passing partial tests can leave a defect).**

$$\exists covered, defects: \operatorname{Set}\left(Bool\right),\\{}\operatorname{Nonempty}\left(covered\right) \land \operatorname{Nonempty}\left(defects\right) \land\\{}\operatorname{Disjoint}\left(covered, defects\right) \land \forall candidate \in Bool,\; candidate \in covered \Rightarrow \neg candidate \in defects.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Audits/PartialTestsLeaveDefect.passing_partial_tests_can_leave_a_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Boolean countermodel uses one covered set and one defect set throughout. Both are nonempty, they are disjoint, and every covered candidate is absent from the defect set.

Consequently the same construction witnesses both successful tests and a surviving defect; no completeness certificate is assumed.

Pinned Mathlib singleton and disjointness lemmas discharge the four public clauses directly. The Lean module introduces no definition.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Audits/PartialTestsLeaveDefect.passing_partial_tests_can_leave_a_defect`
